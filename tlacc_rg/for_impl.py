import os
import re
import logging
import sys
from stmt import *

logging.basicConfig(level=logging.INFO)


# get input lines, convert \t to space, delete line's right spaces
def get_lines(file_path):
    lines = []
    with open(file_path, 'r') as file:
        for line in file:
            if line.strip() != "":
                new_line = line.replace("\t", "  ").rstrip()
                lines.append(new_line)
    return lines


def parse(lines:[str], vars_dict):
    statements = []
    DEFINE_AREA = 1
    FOR_LOOP_AREA = 2
    status = DEFINE_AREA
    i = 0
    length = len(lines)
    while(i < length):
        if lines[i][0].isspace():
            logging.error("Indent Error: " + lines[i])
            sys.exit()

        if isDefinition(lines[i]):
            if status == FOR_LOOP_AREA:
                logging.error("Error Syntax: Definition should be placed at the beginning. " + lines[i])
                sys.exit()
            statement = VarDefineStatement(lines[i], vars_dict)
            statements.append(statement)
            i += 1
        elif isForLoop(lines[i]):
            status = FOR_LOOP_AREA
            for_block = [lines[i]]
            i += 1
            while i<length and lines[i][0].isspace():
                for_block.append(lines[i])
                i += 1
            statement = ForLoopStatement(for_block, vars_dict)
            statements.append(statement)
        elif isRound(lines[i]):
            status = FOR_LOOP_AREA
            statement = RoundStatement(lines[i])
            statements.append(statement)
            i += 1
        elif isMeta(lines[i]):
            statement = MetaStatement(lines[i])
            statements.append(statement)
            i += 1
        else :
            logging.error("Syntax Error: " + lines[i])
            sys.exit()
    return statements
    

def execute(stmts,vars_dict):
    for stmt in stmts:
        tmp_dict = {}
        stmt.execute(tmp_dict)

def get_out_path(input_path):
    dirname = os.path.dirname(input_path)
    filename = os.path.splitext(os.path.basename(input_path))[0]
    filename += ".rounds"   
    output_path = os.path.join(dirname,filename)
    return output_path




