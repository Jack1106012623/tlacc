

# 输入文件路径
# input_path = 'D:\\project\\py-ws\\tlacc_parser\\cc-test\\Raft.in'
# output_path = 'D:\\project\\py-ws\\tlacc_parser\\cc-test\\Raft.round'

import sys
import os

from for_impl import *


def generate(input,output):
    lines = get_lines(input)

    vars_dict = {}
    stmts = parse(lines,vars_dict)

    with open(output,'w') as f:
        sys.stdout = f
        execute(stmts,vars_dict)

def run(file_path):
    abs_file_path = os.path.abspath(file_path)
    if os.path.isfile(file_path):
        output_path = get_out_path(abs_file_path)
        generate(file_path,output_path)
    else:
        print(f"The file '{file_path}' does not exist.")

if __name__ == "__main__":
    # 检查是否提供了文件路径参数
    if len(sys.argv) != 2:
        print("Usage: python run.py <file_path>")
    else:
        file_path = sys.argv[1]
        run(file_path)
