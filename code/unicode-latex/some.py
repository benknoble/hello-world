#! /usr/bin/env python3

import math
import functools


def π(i):
    return functools.reduce(lambda x, y: x + y, str(math.pi).split("."))[i]


pi = π
