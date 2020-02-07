#! /usr/bin/env python3

import functools
import operator


def get_in(m, keys):
    return functools.reduce(operator.getitem, keys, m)
