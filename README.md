# An optimal ternary variable-length edit code

**The maximum number of ternary words of length at most 8 with pairwise Levenshtein distance at least 6 is exactly 8.** Insertion, deletion and substitution each cost one. The empty word is allowed, and the construction attains length 8.

截至 2026 年 11 月 25 日，Sheridan Houghten 的原始码表和 Abraham Yeung 于 11 月 16 日更新的码表，都把这个参数项列为 **8–13**。下界 8 已知。本仓库的贡献是给出排除第九个码字的可复算上界，使该表项取得精确值。这里的文献比较限于可核对的公开来源，学术优先权仍需独立审阅。[Brock 大学三元变长码表](https://www.cosc.brocku.ca/~shoughten/ternaryeditvar.html) · [Yeung 编辑码表](https://abrahamyeung.com/edit-codes/)

## 达到上界的码

下列八个词的 28 对距离全部至少为 6。空串与 `000000` 的距离恰为 6。Lean 在内核中检查了这组码字。[构造与下界](EditCodes/Witness.lean)

```text
ε
000000
00111111
00222222
11001122
11120201
22002211
22210102
```

## 为什么放不下第九个词

两个长度都小于 6 的词总能在至多 5 次编辑内互相转换。先把重叠位置上不同的符号逐个替换，再插入或删除多出的尾部即可。因此，若存在九个码字，至少八个的长度在 6 至 8 之间。

把这类长词作为顶点，两词的编辑距离至少为 6 时连边。图有 $3^6+3^7+3^8=9477$ 个顶点和 8,158,530 条无向边。八个两两相邻的顶点必有三个首字母相同。选定这样的三角形后，剩下五个顶点必须全部落在它的公共邻域内。

Lean 检查三种首字母。对每个三角形，只要公共邻域内还有同首字母的顶点，就保留该分支。否则其余五个顶点只使用另外两种首字母，必有第二个同首字母三角形。在两个三角形的公共邻域内，还必须能找到一条边。检查器穷尽了这些必要条件，结果没有分支通过。[搜索程序](EditCodes/Decision.lean) · [搜索完备性与上界](EditCodes/Reduction.lean)

C++ 复算采用另一种搜索。统一重命名三个字母可以把第一个三角形的首字母变为 0，同时保留每对词的距离。程序穷尽首字母为 0 的 **957,781** 个三角形，在每个公共邻域中直接搜索五个两两相邻的顶点。[独立复算程序](verify.cpp)

## 形式化与复现

主定理 `EditCodes.Ternary.optimal_8_6` 同时给出八词构造，并对任意合法码证明其大小至多为八。距离采用 Wagner–Fischer 递推。Lean 还证明了该递推取得所有对齐方式中的最小代价，以及搜索用的距离表逐项等于这个定义。[主定理](EditCodes.lean) · [距离与码的定义](EditCodes/Basic.lean) · [对齐代价](EditCodes/Alignment.lean) · [距离表正确性](EditCodes/Graph.lean) · [Wagner–Fischer 原文](https://doi.org/10.1145/321796.321811)

使用 Lean 4.19.0 及其标准库。在装有 Elan 的环境中，从仓库根目录运行以下命令。

```sh
lake build
```

上界的最后一次有限计算使用 `native_decide`，因此主定理的信任范围包括 Lean 编译器以及 `Lean.ofReduceBool`。根模块的 `#print axioms` 会列出实际依赖。C++ 程序独立生成图与搜索结果，Lean 构建不读取它的输出。[有限计算](EditCodes/Computation.lean) · [Lean 对原生判定的说明](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide)

用支持 C++20 的编译器可单独复算。

```sh
c++ -O3 -std=c++20 verify.cpp -o verify
./verify
```

本项目的证明设计、实现与文献检索使用了 OpenAI Codex。此版本作为可复现的计算证明公开，尚未经同行评审。
