
from enum import Enum, auto
import logging
import re
import sys
from re_for import *

logging.basicConfig(level=logging.INFO)

def isDefinition(str):
    return not str.startswith("@") and '=' in str

def isForLoop(str:str):
    return str.startswith("for ")

def isRound(str:str):
    return str.startswith('[')

def isMeta(str: str):
    return str.startswith("@")

class StmtType(Enum):
    Var_Define = auto()
    For_Loop = auto()
    Round_Define = auto()

class Statement:

    def __init__(self, indent_level = 0):
        self.indent_level = indent_level

    def parse(self):
        pass

    def execute(self, variables):
        pass

class VarDefineStatement(Statement):
    def __init__(self, line:str, vars_dict):
        self.ori_line = line
        self.line = line.replace(" ","")
        self.variable = ""
        self.value = []
        self.parse(vars_dict)
    
    def parse(self, vars_dict):
        matches = re.fullmatch(Definition_No_Space, self.line)
        if matches:
            # 提取列表中的元素并去除多余空格
            variable, value = self.line.split('=')
            value = value.strip('[]').split(',')
            self.variable = variable
            self.value = value
            if self.variable in vars_dict:
                print("Dumplicate Definition: " + self.ori_line)
                sys.exit()
            else:
                vars_dict[self.variable] = self.value
        else:
            print("Syntax Error: " + self.ori_line)
            sys.exit()
    
    def execute(self, loop_dict):
        pass

class ForLoopStatement(Statement):
    def __init__(self, lines, vars_dict):
        self.ori_lines = lines
        self.lines = lines
        self.vars_dict = vars_dict
        self.loop_variable = ""
        self.loop_range = []
        self.sub_statement = []
        self.parse()

    def parse(self):
        length = len(self.lines)
        i = 0
        self.parse_for_head(self.lines[0])
        i += 1
        if i==length:
            logging.error("Should have Round statement")
            sys.exit()

        indent = self.indent_num(self.lines[i])

        while(i<length):
            line = self.lines[i]
            if self.indent_num(line)!=indent:
                logging.error("Indent Error")
                sys.exit()
            line = line.strip()
            if isRound(line):
                statement = RoundStatement(line)
                self.sub_statement.append(statement)
                i += 1
            elif isForLoop(line):
                for_block = []
                for_block.append(line.strip())
                i += 1
                while i < length and self.indent_num(self.lines[i]) > indent:
                    for_block.append(self.lines[i][indent:])
                    i += 1
                statement = ForLoopStatement(for_block, self.vars_dict)
                self.sub_statement.append(statement)
            else:
                logging.error("Syntax Error: " + self.ori_lines[i])
                sys.exit()

    def parse_for_head(self, line):
        matches = re.fullmatch(For_Loop, line)

        if matches:
            line = line.rstrip(':').rstrip()

            if '[' in line:
                loop_variable = line.split()[1]
                loop_range = line[line.find('[')+1:line.find(']')]
                loop_range = line.replace(" ","")
                loop_range = loop_range.split(',')
                self.loop_variable = loop_variable
                self.loop_range = loop_range
            else:
                _, loop_variable, _, loop_range = line.split()
                if loop_range not in self.vars_dict:
                    logging.error(f"No such variable({loop_range}) {line}")
                    sys.exit()
                self.loop_range = self.vars_dict[loop_range]
                self.loop_variable = loop_variable
            if self.loop_variable in self.vars_dict:
                logging.error(f"duplicate variable({self.loop_variable}) {line}")
                sys.exit()

    def indent_num(self,str):
        return len(str)-len(str.lstrip())

    def execute(self, loop_dict):
        for value in self.loop_range:
            loop_dict[self.loop_variable] = value
            for stmt in self.sub_statement:
                stmt.execute(loop_dict)

class RoundStatement(Statement):
    def __init__(self, line:str):
        self.ori_line = line
        self.line = line.replace(" ","")
        self.parse()

    def parse(self):
        matches = re.fullmatch(New_Round_Without_Space, self.line)
        if matches:
            # 提取列表中的元素并去除多余空格
            sends, rcvs = re.findall(rf'({Actions_Without_Space})', self.line)
            self.sends = Actions(sends)
            self.rcvs = Actions(rcvs)
        else:
            print("Syntax Error: " + self.ori_line)
            sys.exit()

    def execute(self, loop_dict):
        print(f'[{self.sends.print(loop_dict)},{self.rcvs.print(loop_dict)}]')

class MetaStatement(Statement):
    def __init__(self, line:str):
        self.ori_line = line
        self.line = line.replace(" ","")
        self.parse()
    
    def parse(self):
        matches = re.fullmatch(Meta_Msg, self.line)
        # @Msg.Type = Set/Fcn (集合或者函数类型)
        # @Msg.Var = xxx(字符串，为TLA+规约中的信道变量)
        if matches:
            # 提取列表中的元素并去除多余空格
            k, v = self.line.split('=')
            k = k.split('.')[-1]
            if k != "Type" and k != "Var":
                print("Syntax Error, should be Type or Var" + self.ori_line)
                sys.exit()
            elif k == "Type" and v not in {"Set", "Fcn"}:
                print("Syntax Error, Type should be Set or Fcn" + self.ori_line)
        else:
            print("Syntax Error: " + self.ori_line)
            sys.exit()

    def execute(self, loop_dict):
        print(self.line)

class Actions:
    def __init__(self, actions:str):
        self.actions = []
        if '+' in actions:
            strs = actions.split('+')
            for str in strs:
                self.actions.append(Action(str))
        else:
            self.actions.append(Action(actions))
    def print(self, loop_dict):
        str = ""
        length = len(self.actions)
        for i in range(length):
            str += self.actions[i].print(loop_dict)
            if i<length-1:
                str += "+"
        return str

class Action:
    def __init__(self, action:str):
        if '(' in action:
            self.name, left = action.split('(')
            left = left.strip(')')
            self.args = left.split(',')
        else:
            self.name = action
            self.args = []
    def print(self, loop_dict):
        str = self.name
        if len(self.args) >0:
            str += '('
            for i in range(len(self.args)):
                if i>0:
                    str += ','
                if self.args[i] in loop_dict:
                    str += loop_dict[self.args[i]]
                else:
                    str += self.args[i]
            str += ')'
        return str


