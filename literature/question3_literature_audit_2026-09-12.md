# Metered Parking Functions：Question 3 文献核查记录

核查截止日期：2026-09-12。

## 结论与证据边界

在本次能够公开检索并核验的材料中，未找到完整解决 Integers 25 (2025), A73, Question 3 的后续论文、预印本或作者更新。这里的“完整”同时要求任意 t≥1、m≥2、1≤k≤m−1，所有 n≥m−1，次数恰为 k，计数偏好串，并保持新车停妥之后旧车才离开的规则。

这不等于证明不存在未公开、未索引或未能访问的解答，也不是作者关于当前状态的直接确认。检索没有取得可作穷尽性依据的完整引文数据库清单。

## 核心原始来源

### 1. 原问题及原文部分结果
Spencer Daugherty, Pamela E. Harris, Ian Klein, Matt McClinton.
*Metered Parking Functions*. Integers 25 (2025), Paper A73，2025-08-15 发表。

- 期刊 PDF：https://math.colgate.edu/~integers/z73/z73.pdf
- DOI：https://doi.org/10.5281/zenodo.16881806
- arXiv：https://arxiv.org/abs/2406.12941
- 定位：期刊版第32页 Question 3；同页 Proposition 8；Propositions 2–3。
- arXiv 页面在核查时只列出 2024-06-17 的 v1；期刊版题号优先。
- 相关覆盖：Proposition 8 给出 k=1 公式。t≥m−1 时可结合普通停车函数的已知公式处理，见来源6。

### 2. 向量停车函数：不是任意 t 的解答
Melanie Ferreri, Pamela E. Harris, Lucy Martinez, Eric Swartz.
*Enumerating Vector Parking Functions and their Outcomes Based on Specified Lucky Cars*.
arXiv:2508.13917；v1 2025-08-19，v2 2025-09-10。

- 版本及日期：https://arxiv.org/abs/2508.13917
- 本次核验版本：https://arxiv.org/html/2508.13917v2
- Theorem 2.8：普通 PF_{m,n}，m≤n，固定 lucky 集的停车结果数。
- Theorems 5.7、5.11：静态容量向量模型中的偏好串计数，分别固定 lucky 集和 lucky 数。
- 判断：不能把整篇论文说成只计数结果；但未提供向动态 metered 模型的、保持 lucky 统计量的转换。

### 3. 固定 lucky 集：普通停车模型
Pamela E. Harris, Lucy Martinez.
*Parking functions with a fixed set of lucky cars*.
arXiv:2410.08057；核验 v2（2024-12-10）。

- https://arxiv.org/abs/2410.08057
- https://arxiv.org/html/2410.08057v2
- Theorem 3.6：普通 PF_{m,n}，m≤n，固定 lucky 集的偏好串数。
- 判断：固定集合本身不是障碍，偏好串可按集合分拆求和；缺少的是任意 t 的动态模型结论。

### 4. 2026 年引用原论文的工作
Enrica Duchi, Adrián Lillo, Pablo Puerto, Mercedes Rosas, Stefan Trandafir.
*The genesis sequence, tree records and endofunctions*.
arXiv:2601.07938v1，2026-01-12。

- https://arxiv.org/abs/2601.07938
- https://arxiv.org/html/2601.07938v1
- 定位：Section 3.2，Corollary 3.7 前后的讨论。
- 判断：与普通 (n−1,n)-parking functions 的总数关联，不是任意 t 下按 lucky 数细分的多项式定理。

### 5. 原作者 2026 年研究 lucky 统计量的工作
Spencer Daugherty, Jinting Liang.
*Shuffle-compatibility for combinatorial statistics on words, parking functions, and set partitions*.
arXiv:2607.14255v1，2026-07-15。

- https://arxiv.org/abs/2607.14255
- https://arxiv.org/html/2607.14255v1
- 定位：Theorem 4.12、Corollary 4.14。
- 判断：普通停车函数的 lucky 集及 lucky 数之弱 shuffle-compatibility，不是 metered 模型中随车位数变化的计数结论。

### 6. 大 t 区间可以使用的更一般已知公式
Richard P. Stanley, Mei Yin.
*Some Enumerative Properties of Parking Functions*.
arXiv:2306.08681v1（2023）。

- https://arxiv.org/abs/2306.08681
- https://arxiv.org/html/2306.08681
- 定位：Corollary 3.5，取确定性向右停车情形 p=1。
- 推论范围：结合原模型可推出 t≥m−1 时所有 n≥m−1 的要求，包括次数恰为 k；不是一般 t 的完整解答。

### 7. 期刊发表后的作者报告
Matt McClinton. *Metered Parking Functions*.
AMS Fall Central Sectional，2025-10-18。

- 会议页面：https://jcmartinezmori.github.io/events/f25_ams_sectional.html
- 幻灯片：https://jcmartinezmori.github.io/events/f25_ams_sectional_data/slides_mcclinton.pdf
- 定位：PDF 第58页（从1计页）的 “Some Thoughts”。
- 判断：未找到 Question 3 的解答公告；末尾仍邀请读者研究开放问题，但没有逐项确认 Question 3 的当时或当前状态。

## 未完成全文核验的线索

H. Zhu，*New combinatorial aspects of parking functions and sandpile models*，Liverpool，2026。

- 索引所列 PDF：https://livrepository.liverpool.ac.uk/3198583/1/201522764_May2026.pdf
- 搜索摘要可见 metered 模型及文献引用；全文访问失败，没有将其列为已核验或已排除的候选。
- DOI/Zenodo 页面和完整引文数据库访问也不应被理解为已完成穷尽性版本或引文检查。

## 可用于综述的状态表述

“截至2026年9月12日，在可公开检索并核验的后续材料中，未发现完整覆盖 Integers 25 (2025), A73, Question 3 全部条件的解答。已有公式覆盖 k=1，以及由普通停车函数退化得到的 t≥m−1 区间；本次核验的向量停车函数与 fixed-lucky-set 等相关定理不足以解决一般动态情形。”
