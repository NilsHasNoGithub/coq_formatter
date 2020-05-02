"""
Version 0.3
"""

import argparse
from enum import Enum
import sys


def unexpected_eof():
    print("ERROR: unexpected EOF")
    sys.exit(1)

def error(msg):
    print(msg)
    sys.exit(1)

class OperatorType(Enum):
    QUANTIFIER = 1
    ARG_1 = 2
    ARG_2 = 3

class Operator:
    
    def __init__(self, str_rep: str, type_:OperatorType, precedence: int):
        self.str_rep = str_rep
        self.type = type_
        self.precedence = precedence

    def __lt__(self, value):
        return self.precedence < value.precedence

    def __str__(self):
        return self.str_rep


forall = Operator("forall", OperatorType.QUANTIFIER, -500)
exists = Operator("exists", OperatorType.QUANTIFIER, -500)
equiv = Operator("<->", OperatorType.ARG_2, -400)
imp = Operator("->", OperatorType.ARG_2, -300)
disj = Operator("\\/", OperatorType.ARG_2, -200)
conj = Operator("/\\", OperatorType.ARG_2, -100)
negation = Operator("~", OperatorType.ARG_1, -0)

operators = sorted([forall, exists, equiv, imp, disj, conj, negation])


def indent_str(amount, n_spaces, use_tabs):
    if use_tabs:
        return  amount * "\t"
    return amount * (" " * n_spaces)

def skip_comment(content, i):
    while not content[i:].startswith("*)"):
        i+=1
    return i + 2


white_chars = (" ", "\t", "\n")

def d_brack_count(char):
    if char in ('[', '(', '{'):
        return 1
    elif char in (']', ')', '}'):
        return -1
    return 0

def extract_op(definition):
    try:
        for operator in operators:
            left = []

            if definition.startswith(operator.str_rep):
                if operator.type == OperatorType.QUANTIFIER:
                    op_str = []
                    brack_count = 0
                    for char in definition:
                        brack_count += d_brack_count(char)
                        op_str.append(char)
                        if brack_count == 0 and char == ',':
                            break
                    op_str = "".join(op_str + ['\n'])
                else:
                    op_str = operator.str_rep
                right = definition[len(op_str):]
                return "".join(left), op_str, right, operator

            if operator.type == OperatorType.ARG_2:
                brack_count = 0
                for i, char in enumerate(definition):
                    
                    brack_count += d_brack_count(char)
                    left.append(char)

                    if brack_count == 0 and definition[i:].startswith(operator.str_rep):
                        op_str = operator.str_rep + '\n'
                        right = definition[i + len(op_str) - 1:]


                        return "".join(left[:-1]), op_str, right, operator
            
        return None
    except IndexError:
        return None

def enclosed_in_brackets(definition):
    if definition.startswith("(") and definition.endswith(")"):
        bc = 0
        for char in definition[:-1]:
            bc += d_brack_count(char)
            if bc == 0:
                return False
        return True
    return False


def format_def_(definition, cur_indent, n_spaces=4, use_tabs=False, do_indent=True, prev_op_pre=None):
    if definition is None:
        return []
    try:
        ind = indent_str(cur_indent, n_spaces, use_tabs) if do_indent else ""
        new_indent = cur_indent + 1 if do_indent else cur_indent
        while definition[0] in white_chars:
            definition = definition[1:]
        while definition[-1] in white_chars:
            definition = definition[:-1]

        if definition.startswith("(*"):
            comment, i = handle_comment(definition, 0)
            return [ind + comment + '\n'] + format_def_(definition[i:], cur_indent, n_spaces, use_tabs)

        if definition.endswith("*)"):
            comment, i = handle_comment_reverse(definition, len(definition) - 1)
            return format_def_(definition[:i], cur_indent, n_spaces, use_tabs) + [ind + comment + '\n']
        
        if enclosed_in_brackets(definition):
            ind2 = ind if do_indent else indent_str(cur_indent - 1, n_spaces, use_tabs)
            
            return [ind + "(\n"] +\
                format_def_(definition[1:-1], new_indent, n_spaces, use_tabs) +\
                [ind2 + ")\n"]
            
        
        op_extraction = extract_op(definition)
        if op_extraction is not None:
            left, op_str, right, op = op_extraction
            if op.type == OperatorType.ARG_2:
                if prev_op_pre == op.precedence:
                    ind = indent_str(cur_indent - 1, n_spaces, use_tabs)
                    new_indent = cur_indent

                return format_def_(left, new_indent, n_spaces, use_tabs, prev_op_pre=op.precedence) +\
                        [ind + op_str] +\
                        format_def_(right, new_indent, n_spaces, use_tabs, prev_op_pre=op.precedence)
            else:
                return [ind + op_str] + format_def_(right, new_indent, n_spaces, use_tabs, do_indent=op.type==OperatorType.QUANTIFIER)
            
        else:
            return [ind + definition + "\n"]

    except IndexError:
        return [""]

def format_def(definition, n_spaces=4, use_tabs=False):
    #result = format_def_(definition, 1, n_spaces, use_tabs)
    return "".join(format_def_(definition, 1, n_spaces, use_tabs))
    
def handle_format_item(content, i, start_delimiter, n_spaces=4, use_tabs=False):
    formatted = []
    try:
        while not content[i:].startswith(start_delimiter):
            formatted.append(content[i])
            i += 1
        formatted.append(start_delimiter)

        i += len(start_delimiter)

        while content[i] in white_chars:
            formatted.append(content[i])
            if content[i] == '\n':
                break
            i += 1
            

        start_i = i

        while content[i] != ".":
            if content[i:].startswith("(*"):
                i = skip_comment(content, i)
            else:
                i += 1

        fmtd = format_def(content[start_i:i], n_spaces, use_tabs)
       
        formatted.append(fmtd)
        while content[i - 1] in (" ", "\t"):
            i -= 1


    except IndexError:
        unexpected_eof()
    return "".join(formatted), i

def handle_comment_reverse(content, i):
    try:
        comment = []
        while not content[i:].startswith("(*"):
            comment.append(content[i])
            i-=1
        comment.append("(")
        return "".join(reversed(comment)), i
    except IndexError:
        unexpected_eof()

def handle_comment(content, i):
    try:
        comment = []
        while not content[i:].startswith("*)"):
            comment.append(content[i])
            i+=1
        comment.append("*)")
        return "".join(comment), i + 2
    except IndexError:
        unexpected_eof()
    

def format_(content:str, space_amount=4, use_tabs=False):
    out = []
    i = 0
    while i < len(content):

        do_format = False

        if content[i:].startswith("Definition"):
            start_delim = ":="
            do_format = True
        elif content[i:].startswith("Theorem"):
            start_delim = ":"
            do_format = True


        if do_format:
            formatted_def, i = handle_format_item(content, i, start_delim, space_amount, use_tabs)
            out.append(formatted_def)
        elif content[i:].startswith("(*"):
            comment, i = handle_comment(content, i)
            out.append(comment)
        else:
            out.append(content[i])
            i += 1
    return "".join(out)

def main(in_file_p, out_file_p, space_amount=4, use_tabs=False):
    with open(in_file_p, 'r') as f:
        contents = f.read()
    out = format_(contents, space_amount, use_tabs)
    with open(out_file_p, "w") as f:
        f.write(out)
    

if __name__ == '__main__':

    parser = argparse.ArgumentParser(description="Formats a coq file")
    parser.add_argument("input_file", type=str)
    parser.add_argument("output_file", type=str)
    parser.add_argument("--use-tabs", action="store_true", help="sets the script to use tabs instead of spaces")
    parser.add_argument("--spaces", type=int, default=4, help="sets the amount of spaces")
    args = parser.parse_args()
    main(args.input_file, args.output_file, space_amount=args.spaces, use_tabs=args.use_tabs)