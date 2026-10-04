本批归档保存正常 Agent 最近一次运行中，来自五道不同题目的注释异常合并。
运行编号：20261002T162236-1790958156725678901。

这些合并通过了 Lean 验证。异常是输出重复保留了相同的源码注释，
并没有抛出工具异常。failure.json 中 exception_raised=false，
error_type=CommentDuplication；error.txt 记录实际观察到的注释行号。

每个案例目录包含：
  base.lean                实际传给合并工具的主文件。
  donor.lean               实际传给合并工具的、已提取的辅助定理源码。
  candidate.lean           合并输出，与历史下一轮任务输入的 SHA-256 一致。
  donor_submitted.lean     历史辅助定理 prover 提交的完整源码。
  explorer_submitted.lean  合并前最近一次 explorer 提交的完整源码。
  result.json              重放合并工具得到的完整结果，包括验证和公理信息。
  failure.json             调用参数、原始记录路径、统计、注释行号和文件哈希。
  error.txt                注释异常说明。

brualdi_ch10_60 选取连续两次合并中的第二次；prefix_* 文件记录第一
次合并，说明其 base.lean 如何由历史 explorer 提交还原。其余案例
均使用所选 explorer 提交后的第一次合并。imosl_2015_c6 选取第五次
重复运行中的首次异常合并，保留较小输入，便于后续调试。

manifest.json 列出五个案例及其合并前后的行数、注释数量和输出哈希。
注释统计只计算去除行首缩进后的 -- 单行注释，不统计块注释。
excess_comment_lines 表示输出出现次数超出两个输入各自最大次数的
注释行数量。它用于定位重复复制，不代表所有同文注释都应删除。

从 AgentProver 根目录重放全部案例：
  .venv/bin/python tools/lean_merge/failure_archives/comment_duplication_20261002/reproduce.py --jobs 3

重放一个案例：
  .venv/bin/python tools/lean_merge/failure_archives/comment_duplication_20261002/reproduce.py comment_duplication_hackmath_10_round002

默认使用 failure.json 中记录的已构建 Mathlib 项目和超时。
可用 --project /path/to/project 与 --timeout 1200 覆盖。
工具链为 leanprover/lean4:v4.26.0。

重放不修改归档输入或输出，也不创建新的失败记录。退出码 0 表示
所选案例均通过 Lean 验证、与历史输出哈希一致且再次产生注释异常。
修复工具后，异常消失或输出变化都会使这个诊断脚本返回退出码 1，
此时应读取输出中的各项检查结果。
