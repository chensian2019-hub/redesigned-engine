#!/usr/bin/env python3
"""A small, modular interpreter for the mini-Scheme language in spec.md."""
from __future__ import annotations

import math
import json
import re
import sys
from dataclasses import dataclass
from functools import reduce
from operator import mul


@dataclass(frozen=True)
class Symbol:
    name: str


class _Nil:
    def __repr__(self) -> str:
        return "()"


NIL = _Nil()


@dataclass
class Pair:
    car: object
    cdr: object


def tokenize(source: str) -> list[str]:
    """Split source while preserving strings and removing semicolon comments."""
    tokens, i = [], 0
    while i < len(source):
        c = source[i]
        if c.isspace():
            i += 1
        elif c == ';':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif c in "()'":
            tokens.append(c)
            i += 1
        elif c == '"':
            start, i = i, i + 1
            escaped = False
            while i < len(source):
                if source[i] == '"' and not escaped:
                    i += 1
                    break
                if source[i] == '\\' and not escaped:
                    escaped = True
                else:
                    escaped = False
                i += 1
            else:
                raise SyntaxError("unterminated string")
            tokens.append(source[start:i])
        else:
            start = i
            while i < len(source) and not source[i].isspace() and source[i] not in "();'\"":
                i += 1
            tokens.append(source[start:i])
    return tokens


def read_all(source: str) -> list[object]:
    tokens, pos = tokenize(source), 0

    def read() -> object:
        nonlocal pos
        if pos >= len(tokens):
            raise SyntaxError("unexpected end of input")
        token = tokens[pos]
        pos += 1
        if token == "(":
            items = []
            while pos < len(tokens) and tokens[pos] != ")":
                if tokens[pos] == ".":
                    pos += 1
                    tail = read()
                    if pos >= len(tokens) or tokens[pos] != ")":
                        raise SyntaxError("malformed dotted pair")
                    pos += 1
                    result = tail
                    for item in reversed(items):
                        result = Pair(item, result)
                    return result
                items.append(read())
            if pos >= len(tokens):
                raise SyntaxError("missing )")
            pos += 1
            return list_to_pair(items)
        if token == ")":
            raise SyntaxError("unexpected )")
        if token == "'":
            return list_to_pair([Symbol("quote"), read()])
        if token.startswith('"'):
            # Scheme strings use the common escapes listed in the specification.
            return json.loads(token)
        if token == "#t":
            return True
        if token == "#f":
            return False
        if re.fullmatch(r"[+-]?\d+", token):
            return int(token)
        if re.fullmatch(r"[+-]?(?:\d+\.\d*|\.\d+)(?:[eE][+-]?\d+)?", token):
            return float(token)
        return Symbol(token)

    forms = []
    while pos < len(tokens):
        forms.append(read())
    return forms


def list_to_pair(items: list[object], tail: object = NIL) -> object:
    for item in reversed(items):
        tail = Pair(item, tail)
    return tail


def pair_to_list(value: object) -> list[object]:
    result = []
    while isinstance(value, Pair):
        result.append(value.car)
        value = value.cdr
    if value is not NIL:
        raise TypeError("expected a proper list")
    return result


def write(value: object) -> str:
    if value is NIL:
        return "()"
    if value is True:
        return "#t"
    if value is False:
        return "#f"
    if isinstance(value, Symbol):
        return value.name
    if isinstance(value, str):
        return '"' + value.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\t', '\\t').replace('\r', '\\r') + '"'
    if isinstance(value, Pair):
        parts, cur = [], value
        while isinstance(cur, Pair):
            parts.append(write(cur.car))
            cur = cur.cdr
        return "(" + " ".join(parts) + ("" if cur is NIL else " . " + write(cur)) + ")"
    if isinstance(value, float):
        return str(int(value)) if value.is_integer() else repr(value)
    if callable(value):
        return "#<procedure>"
    return str(value)


class Environment:
    def __init__(self, outer: Environment | None = None):
        self.data: dict[str, object] = {}
        self.outer = outer

    def find(self, name: str) -> Environment:
        if name in self.data:
            return self
        if self.outer is not None:
            return self.outer.find(name)
        raise NameError(f"unbound symbol: {name}")

    def get(self, name: str) -> object:
        return self.find(name).data[name]


@dataclass
class Closure:
    parameters: list[str]
    body: list[object]
    environment: Environment


class Primitive:
    def __init__(self, name: str, fn, display: bool = False):
        self.name, self.fn, self.display = name, fn, display

    def __call__(self, args: list[object]) -> object:
        return self.fn(*args)


def truthy(value: object) -> bool:
    return value is not False


def apply(proc: object, args: list[object], output) -> object:
    if isinstance(proc, Primitive):
        if proc.display:
            return proc.fn(*args, output=output)
        return proc(args)
    if isinstance(proc, Closure):
        if len(args) != len(proc.parameters):
            raise TypeError("wrong number of arguments")
        env = Environment(proc.environment)
        env.data.update(zip(proc.parameters, args))
        result = None
        for form in proc.body:
            result = evaluate(form, env, output)
        return result
    raise TypeError("attempt to call a non-procedure")


def evaluate(expr: object, env: Environment, output) -> object:
    if isinstance(expr, Symbol):
        return env.get(expr.name)
    if not isinstance(expr, Pair):
        return expr
    forms = pair_to_list(expr)
    if not forms:
        return NIL
    head = forms[0]
    name = head.name if isinstance(head, Symbol) else None
    args = forms[1:]
    if name == "quote":
        return args[0]
    if name == "if":
        test = evaluate(args[0], env, output)
        if truthy(test):
            return evaluate(args[1], env, output)
        return evaluate(args[2], env, output) if len(args) > 2 else None
    if name == "cond":
        for clause in args:
            parts = pair_to_list(clause)
            if parts[0] == Symbol("else"):
                return sequence(parts[1:], env, output)
            test = evaluate(parts[0], env, output)
            if truthy(test):
                return sequence(parts[1:], env, output) if len(parts) > 1 else test
        return None
    if name in ("and", "or"):
        result = True if name == "and" else False
        for form in args:
            result = evaluate(form, env, output)
            if (name == "and" and not truthy(result)) or (name == "or" and truthy(result)):
                return result
        return result
    if name == "define":
        if isinstance(args[0], Pair):
            sig = pair_to_list(args[0])
            symbol, params = sig[0], sig[1:]
            closure = Closure([p.name for p in params], args[1:], env)
            env.data[symbol.name] = closure
            return symbol
        symbol = args[0]
        env.data[symbol.name] = evaluate(args[1], env, output)
        return symbol
    if name == "lambda":
        params = [p.name for p in pair_to_list(args[0])]
        return Closure(params, args[1:], env)
    if name == "let":
        bindings = pair_to_list(args[0])
        names, values = [], []
        for binding in bindings:
            pair = pair_to_list(binding)
            names.append(pair[0].name)
            values.append(evaluate(pair[1], env, output))
        local = Environment(env)
        local.data.update(zip(names, values))
        return sequence(args[1:], local, output)
    if name == "begin":
        return sequence(args, env, output)
    proc = evaluate(head, env, output)
    values = [evaluate(arg, env, output) for arg in args]
    return apply(proc, values, output)


def sequence(forms: list[object], env: Environment, output) -> object:
    result = None
    for form in forms:
        result = evaluate(form, env, output)
    return result


def scheme_equal(a: object, b: object) -> bool:
    if type(a) is not type(b):
        return False
    if isinstance(a, Pair):
        return scheme_equal(a.car, b.car) and scheme_equal(a.cdr, b.cdr)
    if a is NIL or b is NIL:
        return a is b
    return a == b


def make_global(output) -> Environment:
    env = Environment()
    def bind(name, fn, display=False):
        env.data[name] = Primitive(name, fn, display)
    bind("+", lambda *xs: sum(xs))
    bind("-", lambda x, *xs: -x if not xs else x - sum(xs))
    bind("*", lambda *xs: reduce(mul, xs, 1))
    def divide(*xs):
        if len(xs) == 1:
            return 1 / xs[0]
        result = xs[0]
        for x in xs[1:]:
            result = result / x
        if all(isinstance(x, int) and not isinstance(x, bool) for x in xs):
            return math.trunc(result)
        return result
    bind("/", divide)
    bind("modulo", lambda a, b: a % b)
    bind("quotient", lambda a, b: math.trunc(a / b))
    bind("expt", pow)
    bind("abs", abs)
    for op, fn in (("=", lambda a,b:a==b), ("<", lambda a,b:a<b), (">", lambda a,b:a>b), ("<=", lambda a,b:a<=b), (">=", lambda a,b:a>=b)):
        bind(op, lambda *xs, f=fn: all(f(a,b) for a,b in zip(xs, xs[1:])))
    bind("not", lambda x: not truthy(x))
    bind("cons", lambda a,b: Pair(a,b))
    bind("car", lambda p: p.car)
    bind("cdr", lambda p: p.cdr)
    bind("list", lambda *xs: list_to_pair(list(xs)))
    bind("length", lambda x: len(pair_to_list(x)))
    bind("append", lambda *xs: list_to_pair(sum((pair_to_list(x) for x in xs), [])))
    bind("null?", lambda x: x is NIL)
    bind("pair?", lambda x: isinstance(x, Pair))
    bind("list?", lambda x: is_list(x))
    bind("number?", lambda x: isinstance(x, (int,float)) and not isinstance(x,bool))
    bind("boolean?", lambda x: isinstance(x,bool))
    bind("symbol?", lambda x: isinstance(x,Symbol))
    bind("string?", lambda x: isinstance(x,str))
    bind("procedure?", lambda x: isinstance(x,(Primitive,Closure)))
    bind("zero?", lambda x: x == 0)
    bind("even?", lambda x: x % 2 == 0)
    bind("odd?", lambda x: x % 2 != 0)
    bind("eq?", eq_value)
    bind("equal?", scheme_equal)
    bind("display", display_value, True)
    bind("newline", newline_value, True)
    return env


def is_list(value: object) -> bool:
    while isinstance(value, Pair):
        value = value.cdr
    return value is NIL


def eq_value(a: object, b: object) -> bool:
    if type(a) is not type(b):
        return False
    if isinstance(a, (int, float, bool, Symbol)):
        return a == b
    if a is NIL or b is NIL:
        return a is b
    return a is b


def display_value(value: object, output) -> None:
    output.write(value if isinstance(value, str) else write(value))
    return None


def newline_value(output) -> None:
    output.write("\n")
    return None


def main(argv: list[str]) -> int:
    sources = []
    if argv:
        for filename in argv:
            with open(filename, encoding="utf-8") as f:
                sources.append(f.read())
    else:
        sources.append(sys.stdin.read())
    env = make_global(sys.stdout)
    for source in sources:
        for form in read_all(source):
            result = evaluate(form, env, sys.stdout)
            if result is not None:
                print(write(result))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (SyntaxError, TypeError, ValueError, NameError, ZeroDivisionError, IndexError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        raise SystemExit(1)
