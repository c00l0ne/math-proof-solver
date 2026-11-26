"""Canonical proof terms and exact rational constants; no expression parser."""
import hashlib
import json
from fractions import Fraction


class Unsupported(ValueError):
    pass

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))

def digest(value):
    return hashlib.sha256(canonical(value).encode("utf-8")).hexdigest()

def freeze(value):
    if type(value) is tuple:
        # A hashable plain tuple cannot contain a list at any depth, so it is already frozen.
        try:
            hash(value)
            return value
        except TypeError:
            pass
    if isinstance(value, (tuple, list)):
        return tuple(freeze(x) for x in value)
    return value

def same(a, b):
    return canonical(a) == canonical(b)

def q(n, d=1):
    f = Fraction(n, d)
    return ("q", f.numerator, f.denominator)

def rational(e):
    if not (isinstance(e, (tuple, list)) and len(e) == 3 and e[0] == "q"
            and type(e[1]) is int and type(e[2]) is int and e[2] > 0):
        raise Unsupported("Ожидалось точное рациональное число")
    if tuple(e) != q(e[1], e[2]):
        raise Unsupported("Неканоническая рациональная константа")
    return Fraction(e[1], e[2])

def size(e):
    return 1 + sum(size(x) for x in e[1:]) if isinstance(e, (tuple, list)) else 1

def match(pattern, value, env):
    if isinstance(pattern, str) and pattern.startswith("?"):
        if pattern in env:
            return same(env[pattern], value)
        env[pattern] = freeze(value)
        return True
    if isinstance(pattern, (tuple, list)):
        return (isinstance(value, (tuple, list)) and len(pattern) == len(value)
                and all(match(p, v, env) for p, v in zip(pattern, value)))
    return same(pattern, value)

def instantiate(template, env):
    if isinstance(template, str) and template.startswith("?"):
        return env[template]
    if isinstance(template, (tuple, list)):
        return tuple(instantiate(x, env) for x in template)
    return template

ZERO, ONE = q(0), q(1)
