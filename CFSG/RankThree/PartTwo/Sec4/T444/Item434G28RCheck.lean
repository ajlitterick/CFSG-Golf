module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Bin
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28


@[expose] def invols (S : Array ℕ) : Array ℕ := S.filter fun s => s != id2 && mul2 s s == id2

@[expose] def ord3s (S : Array ℕ) : Array ℕ := S.filter fun s => s != id2 && pw2 s 3 == id2


end CFSG.RankThree.PartTwo.Sec4.Item434G28
