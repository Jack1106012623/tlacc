TLACC RG(Round Generator)：从有损同步执行定义语言(`*.in`文件)生成TLACC配置文件(`*.rounds`文件)

## 用法

输入：`python3 run.py ./tests/Raft.in`

生成 `./tests/Raft.rounds` 文件

`tests`目录下含有一些示例


## 语句
支持四种语句

第一种是赋值：
```
key = [v1,v2] (该语句定义一个变量key为一个列表)
```

第二种是for循环：
```
for i in key:
    [Send(i,*), NULL]
    [Send(i,*), Rcv(*,*)]
```
第三种是Round定义：
```
[Send(i,*), NULL]
[Send(i,*), Rcv(*,*)]
```

第四种是信道描述：包括信道变量名称和信道类型
```
@Msg.Type = Set/Fcn (集合或者函数类型)
@Msg.Var = xxx(字符串，为TLA+规约中的信道变量)
```