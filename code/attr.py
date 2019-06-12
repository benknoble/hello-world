#! /usr/bin/env python3

import re


class Attr(object):

    def __init__(self, value):
        self.value = value

    @property
    def name(self):
        class_name = type(self).__name__
        readable_name = ' '.join(re.findall('[A-Z][^A-Z]*', class_name))
        return readable_name


# class Strength(Attr): pass
class Dexterity(Attr): pass
class Constitution(Attr): pass
class Wisdom(Attr): pass
class Intelligence(Attr): pass
class Charisma(Attr): pass

# but why...
Strength = type("Strength", (Attr,), {})

class PassivePerception(Attr): pass


if __name__ == '__main__':
    char = [Strength(15), Dexterity(12), Constitution(14), Wisdom(11),
            Intelligence(11), Charisma(8), PassivePerception(10)]
    for a in char:
        print({a.name: a.value})
