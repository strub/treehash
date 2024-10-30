#! /usr/bin/env python3

# ------------------------------------------------------------------------
import dataclasses as dc
import math
import typing as tp

# ------------------------------------------------------------------------
@dc.dataclass
class Node:
    level  : int
    offset : int

    @property
    def isleft(self):
        return self.offset % 2 == 0

    @property
    def isright(self):
        return not self.isleft

    @property
    def parent(self):
        return Node(self.level + 1, self.offset // 2)

# ------------------------------------------------------------------------
@dc.dataclass
class TCNode:
    node : Node
    hash : any

# ------------------------------------------------------------------------
class TreeHash:
    def __init__(self, height: int, start: int = 0, big : bool = False, stack = None):
        assert (0 <= height)
        self.height = height
        self.stack  = [] if stack is None else stack
        self.start  = start
        self.leaf   = 0
        self.big    = big
        self.depth  = 0
        self.base   = len(self.stack)
        self.result = None

    def _reducible(self):
        if self.depth < 2:
            return False
        return self.stack[-1].node.level == self.stack[-2].node.level
    
    @staticmethod
    def _merge(node1 : TCNode, node2: TCNode) -> TCNode:
        hash = (node1.hash, node2.hash)
        node1, node2 = node1.node, node2.node

        assert(node1.level == node2.level)
        assert(node1.level >= 0)
        assert(node2.offset == node1.offset + 1)
        assert(node1.offset & 0b1 == 0)

        return TCNode(
            node = Node(
                level  = node1.level + 1,
                offset = node1.offset // 2
            ),
            hash = hash,
        )
    
    @property
    def done(self):
        return self.result is not None

    @property
    def isinit(self):
        return self.depth > 0

    @property
    def active(self):
        return len(self.stack) == self.depth + self.base

    @property
    def low(self):
        if self.done:
            return math.inf
        if self.depth > 0:
            return self.stack[self.base + self.depth - 1].node.level
        return self.height
    
    def reduce(self):
        try:
            while True:
                self.__next__()
        except StopIteration:
            pass

    def __iter__(self):
        return self

    def __next__(self):
        assert(self.active)

        if self.done:
            raise StopIteration

        def reduce():
            node1 = self.stack.pop()
            node2 = self.stack.pop()
            self.stack.append(self._merge(node2, node1))
            self.depth -= 1

        if self._reducible():
            assert (not self.big)
            reduce()
        else:
            node = Node(level = 0, offset = self.leaf + self.start)
            self.leaf += 1
            self.stack.append(TCNode(node = node, hash = node))
            self.depth += 1
            if self.big:
                while self._reducible():
                    reduce()

        if self.leaf == 1 << self.height:
            if self.depth == 1:
                self.result = self.stack.pop()
                self.depth = 0
                return self.result

        return self.stack[-1]
    
    def __repr__(self):
        return repr(dict(
            height = self.height,
            leaf   = self.leaf,
            big    = self.big,
            base   = self.base,
            depth  = self.depth,
            done   = self.done,
            active = self.active,
            low    = self.low,
            ls     = len(self.stack),
            result = self.result,
            stack  = self.stack,
        ))
    
# ------------------------------------------------------------------------
class ClassicalAuthPath:
    def __init__(self, height: int):
        assert (0 < height)
        self.height = height
        self.index  = -1
        self.auth   = None
        self.stack  = None

    def __iter__(self):
        return self
    
    def __next__(self):
        def treehash(height : int, start: int = 0, pump: int = 0):
                th = iter(TreeHash(height, start = start))
                for _ in range(pump):
                    next(th)
                return th

        if self.index+1 == 1 << self.height:
            raise StopIteration

        if self.index < 0:
            self.auth  = [Node(i, 1) for i in range(self.height)]
            self.stack = [treehash(i, pump = 1) for i in range(self.height)]
            self.index = 0
        else:
            for h in range(self.height):                
                p  = 1 << h
                if (self.index + 1) % p != 0:
                    continue
                assert (self.stack[h].done)
                self.auth[h] = self.stack[h].stack[0].node
                self.stack[h] = treehash(h, start = (self.index + 1 + p) ^ p)

            for h in range(self.height):
                try:
                    for _ in range(2):
                        if self.stack[h].done:
                            break
                        next(self.stack[h])
                except StopIteration:
                    assert False

            self.index += 1

        return self.auth[::-1]

# ------------------------------------------------------------------------
class LogAuthPath:
    def __init__(self, height: int):
        assert (0 < height)
        self.height = height
        self.index  = -1
        self.auth   = None
        self.stack  = None

    def __iter__(self):
        return self
    
    def __next__(self):
        def treehash(height : int, start: int = 0, pump: int = 0):
                th = iter(TreeHash(height, start = start))
                for _ in range(pump):
                    next(th)
                return th

        if self.index+1 == 1 << self.height:
            raise StopIteration

        if self.index < 0:
            self.auth  = [Node(i, 1) for i in range(self.height)]
            self.stack = [treehash(i, pump = 1) for i in range(self.height)]
            self.index = 0
        else:
            for h in range(self.height):
                p  = 1 << h
                if (self.index + 1) % p != 0:
                    continue
                assert (self.stack[h].done)
                self.auth[h] = self.stack[h].stack[0].node
                self.stack[h] = treehash(h, start = (self.index + 1 + p) ^ p)

            try:
                for _ in range(2*self.height):
                    focus = min(
                        range(self.height),
                        key = lambda i : self.stack[i].low
                    )
                    next(self.stack[focus])

            except StopIteration:
                pass

            self.index += 1

        return self.auth[::-1]

# ------------------------------------------------------------------------
class PfffAuthPath:
    def __init__(self, height: int, K: int):
        assert (0 < height)
        assert (2 <= K and K <= height)
        assert ((height - K) % 2 == 0)

        self.height   = height
        self.index    = -1
        self.K        = K
        self.stack    = []
        self.keep     = [None] * (height-1)
        self.auth     = [None] * height
        self.retain   = [[] for _ in range(self.K - 1)]
        self.treehash = [None] * (height - K)

    def __iter__(self):
        return self

    def __next__(self):
        if self.index+1 == 1 << self.height:
            raise StopIteration

        if self.index < 0:
            self.index = 0

            for h in range(self.height):
                self.auth[h] = TCNode(node = Node(h, 1), hash = None)

            for h in range(self.height - self.K):
                self.treehash[h] = TreeHash(
                    height = h,
                    start  = 3 << h,
                    stack  = self.stack,
                )
                self.treehash[h].reduce()

            for h in range(self.height - self.K, self.height - 1):
                for j in range((1 << (self.height-h-1)) - 2, -1, -1):
                    self.retain[h-(self.height-self.K)] \
                        .append(TCNode(node = Node(h, 2*j+3), hash = None))

        else:
            tau = Node(0, self.index)

            while not tau.isleft:
                tau = tau.parent

            assert (tau.level < self.height)

            if tau.level < self.height - 1:
                if tau.parent.isleft:
                    self.keep[tau.level] = self.auth[tau.level]
                    assert(self.keep[tau.level].node.level == tau.level)

            if tau.level == 0:
                self.auth[0] = TCNode(node = tau, hash = 'tau0')

            else:
                self.auth[tau.level] = TreeHash._merge(
                    self.auth[tau.level-1], self.keep[tau.level-1])
                self.keep[tau.level-1] = None

                for h in range(tau.level):
                    if h < self.height - self.K:
                        assert(self.treehash[h].done)
                        assert(self.treehash[h].result.node.level == h)
                        self.auth[h] = self.treehash[h].result
                        self.treehash[h] = None
                    else:
                        self.auth[h] = self.retain[h - (self.height - self.K)].pop()

                for h in range(tau.level):
                    if h == self.height - self.K:
                        break
                    self.treehash[h] = TreeHash(
                        height = h,
                        start  = self.index + 1 + (3 << h),
                        stack  = self.stack,
                        big    = True,
                    )
                    # next(self.treehash[h])

                for h in range(self.height - self.K):
                    stacks = [
                        (i, tc) for i, tc in enumerate(self.treehash)
                        if tc is not None and not tc.done
                    ]
                    if not stacks:
                        break
                    focus = min(
                        range(len(stacks)),
                        key = lambda i : stacks[i][1].low
                    )
                    next(stacks[focus][1])

            self.index += 1

        return [x.node for x in self.auth[::-1]]

# ------------------------------------------------------------------------
for x in iter(PfffAuthPath(16, 8)):
    pass
