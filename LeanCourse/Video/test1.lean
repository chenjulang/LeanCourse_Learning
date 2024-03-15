
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
:= by
  simp?
  -- simp only [add_assoc, add_left_comm, add_comm]
