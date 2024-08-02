from dataclasses import dataclass, field
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
    body: "Statement"


Statement: TypeAlias = None | Assignment | If | While | list["Statement"]
