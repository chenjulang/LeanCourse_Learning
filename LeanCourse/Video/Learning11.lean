

-- 正交性：
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0
