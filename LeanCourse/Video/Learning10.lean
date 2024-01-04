
-- 特征向量和特征值
-- 如何引入这个话题很重要，其实可以单独出一个视频，这样更加吸引人

def HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0
