import re

Blank = r'\s*'
Blanks = r'\s+'
Identifier = r'\w+'
Value = r'\w+'
Equal = r'='
List_No_Space = rf'\[{Value}(,{Value})*\]'
List = rf'\[{Blank}{Value}{Blank}(,{Blank}{Value}{Blank})*\]'

ARG = rf'(?:{Identifier}|\*)'
ARGS_Without_Space = rf'\({ARG}(?:,{ARG})*\)'
Action_Without_Space = rf'{Identifier}(?:{ARGS_Without_Space})*'
Round_Without_Space = rf'\[{Action_Without_Space},{Action_Without_Space}\]'

Actions_Without_Space = rf'{Action_Without_Space}(?:\+{Action_Without_Space})*'
New_Round_Without_Space = rf'\[{Actions_Without_Space},{Actions_Without_Space}\]'


Definition_No_Space = rf'{Identifier}{Equal}{List_No_Space}$'
For_Loop = rf'^for{Blanks}{Identifier}{Blanks}in{Blanks}({Identifier}|{List}){Blank}:{Blank}'
Round= rf'\[{Blank}{Identifier}\]'

# No space
# @Msg.Type = Set/Fcn (集合或者函数类型)
# @Msg.Var = xxx(字符串，为TLA+规约中的信道变量)
Meta_Msg = rf'@Msg\.(\w+)=(\w+)'


#### 正则表达式功能测试

# 输入字符串
# input_string = "[ v 1, 1, s2 ]"

# # 正则表达式模式
# pattern = r'^(null|or)$'

# input_string = "for i in [ v1 , v2 , v3] :"
# matches = re.match(For_Loop, input_string)

# if matches:
#     print("匹配")
#     line = matches[0].rstrip(':').strip()
#     line = line[line.find('[')+1:line.find(']')]
#     loop_range = line.replace(" ","")
#     loop_range = loop_range.strip('[]').split(',')
            
# print(1)

# print("TTTTTT")


# matches = re.fullmatch(Meta_Msg, "@Msg.Type=Set")
# if matches:
#     print("Msg.Type 匹配")
#     print(matches)
# else:
#     print("Msg.Type 不匹配")


# matches = re.fullmatch(Actions_Without_Space, "Send(i,*)+Rcv+Send(*)")
# if matches:
#     print("Action 匹配")
#     print(matches)
# else:
#     print("Action 不匹配")



# input_string = "[Send(i,*), Rcv(1,*)+Rcv]"
# input_string = input_string.replace(" ","")

# matches = re.fullmatch(New_Round_Without_Space, input_string)
# if matches:
#     print("Round 匹配")
#     tmp = re.findall(Action_Without_Space, input_string)
#     print(tmp)
# else:
#     print("Round 不匹配")

