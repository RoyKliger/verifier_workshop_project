from verifier_workshop_project.commands.commands import Command, AssignCommand, SeqCommand, SkipCommand, IfCommand, WhileCommand
import z3

def parse_command(command: str) -> Command:
    return parse_command_rec(command.split())

def parse_command_rec(tokens) -> Command:
    if tokens[0] == "skip":
        return SkipCommand()
    elif tokens[0] == "if":
        cond = z3.parse_smt2_string(tokens[1])
        c1 = parse_command_rec(tokens[3:])
        c2 = parse_command_rec(tokens[3 + len(str(c1).split()) + 1:])
        return IfCommand(cond, c1, c2)
    elif tokens[0] == "while":
        cond = z3.parse_smt2_string(tokens[1])
        inv = z3.parse_smt2_string(tokens[3])
        body = parse_command_rec(tokens[5:])
        return WhileCommand(cond, body, inv)
    elif tokens[1] == ":=":
        var = z3.Int(tokens[0])
        expr = z3.parse_smt2_string(" ".join(tokens[2:]))
        return AssignCommand(var, expr)
    elif tokens[1] == ";":
        c1 = parse_command_rec(tokens[0])
        c2 = parse_command_rec(tokens[2:])
        mid = z3.Bool("mid")
        return SeqCommand(c1, c2, mid)
    else:
        raise Exception("Invalid command")