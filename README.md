
这个项目基于模型检验工具[TLC](https://github.com/tlaplus/tlaplus)开发了检测TLA+规约有损同步执行的工具 TLACC。

tlacc_v2分支目前具有一个可使用的版本(tlacctools-20240409)，tlacc_v3分支在进行代码优化和美化。

目录`tlacc_rg`中含有一个用python编写的 round 生成器，和一些使用示例。

仓库 [tlacc_exp](https://github.com/Jack1106012623/tlacc_exp/tree/master) 正在进行案例研究。

<!-- The project is to develop a model checker called TLACC for verifying the lossy synchronous execution of TLA+ specifications.
TLACC is developed based on .
The branch tlacc_v2 currently has a version to use.
The branch tlacc_v3 is doing some optimization to increase readability and efficiency.

Dir `tlacc_rg/` has a round generator written in python and some examples. -->

命令参数：与TLC的命令参数一致，只需要额外添加参数`-rounds filename.rounds`，指示有损同步执行的定义。目前tlacc必须添加参数`-rounds`，若要运行原版TLC，需要使用TLC的Jar包，参见[TLC](https://github.com/tlaplus/tlaplus)。

TODO
------------
- Make the code easy to read and use.
- Optimize efficiency.







