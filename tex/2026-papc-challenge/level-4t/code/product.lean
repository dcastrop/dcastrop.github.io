namespace Sets
-- A row of the product is a pair x: x.1 a row of R, x.2 a row of S
def product {α β : Type} (R : Table α) (S : Table β) : Table (α × β) :=
  fun x => R x.1 ∧ S x.2

-- The image f[R]: the rows s with s = f t for some row t of R
def image {α β : Type} (f : α → β) (R : Table α) : Table β :=
  fun s => ∃ t, R t ∧ f t = s
end Sets
