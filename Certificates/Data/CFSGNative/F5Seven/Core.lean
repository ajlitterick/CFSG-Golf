module

@[expose] public section

namespace Certificates.F5Seven

abbrev Tup7 := Fin 7 × Fin 7 × Fin 7 × Fin 7


def detT (x : Tup7) : Fin 7 := x.1 * x.2.2.2 - x.2.1 * x.2.2.1


def zeta7 : Tup7 := (1, 5, 2, 1)

def sigma7 : Tup7 := (1, 0, 0, 6)


end Certificates.F5Seven

end
