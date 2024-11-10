from dataclasses import dataclass
from typing import TypeAlias

@dataclass
class Identifier:
    name: str


@dataclass
class BinaryIntExpr:
    left: "IntExpr"
    op: str
    right: "IntExpr"


IntExpr: TypeAlias = Identifier | int | BinaryIntExpr

@dataclass
class Comparison:
    left: IntExpr
    op: str
    right: IntExpr

@dataclass
class BinaryBoolExpr:
    left: "BoolExpr"
    op: str
    right: "BoolExpr"


BoolExpr: TypeAlias = Identifier | bool | Comparison | BinaryBoolExpr

@dataclass
class Assignment:
    variable: Identifier
    value: IntExpr


@dataclass
class If:
    condition: BoolExpr
    if_true: "Statement"
    if_false: "Statement"


@dataclass
class While:
    condition: BoolExpr
    invariant: BoolExpr
    body: "Statement"


@dataclass
class For:
    start: "Statement"
    end: BoolExpr
    diff: "Statement"
    invariant: BoolExpr
    body: "Statement"


Statement: TypeAlias = None | Assignment | If | While | For | list["Statement"]
