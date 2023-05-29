import org.tpolecat.typename.TypeName

object TikTakToe {

    trait Nat
    class _0 extends Nat // "numbers" zero at the type level
    class Succ[N <: Nat] extends Nat // 2023 == Succ[Succ[Succ[...Succ[_0]]]]
    type _1 = Succ[_0]
    type _2 = Succ[_1]
    type _3 = Succ[_2]
    type _4 = Succ[_3]
    type _5 = Succ[_4]

    // Player
    type Player = "X" | "O"
    type Cell = Player | "_"

    // type level list
    trait HList
    class HNil extends HList // empty list
    infix class ::[H, T <: HList] extends HList

    // board
    type Board = HList
    type EmptyRow = "_" :: "_" :: "_" :: HNil // ::["_", ::["_", ::["_", HNill]]]
    type EmptyBoard = EmptyRow :: EmptyRow :: EmptyRow :: HNil

    // satisfying predicates
    trait Length[L <: HList, N <: Nat] // Length[L, N] exists if the length of L is N
    given zeroLength: Length[HNil, _0] with {} // axiom
    given lengthInductive[H, T <: HList, N <: Nat](using Length[T, N]): Length[H::T, Succ[N]] with {}
    // prolog style of programming

    // who wins in a game of tic-tac-toe?
    // winner by row
    trait SameValues[L <: HList, V]
    given svBasic[V]: SameValues[HNil, V] with {}
    given svInductive[T <: HList, V](using SameValues[T, V]): SameValues[V :: T, V] with {}

    trait WinsByRow[B <: Board, W <: Player]
    given winsFirstRow[R <: HList, RT <: HList, P <: Player](using SameValues[R, P]): WinsByRow[R :: RT, P] with {}
    given winsAnyRow[R <: HList, RT <: HList, P <: Player](using WinsByRow[RT, P]): WinsByRow[R :: RT, P] with {}

    // winner by column
    // take nth element
    trait TakeNth[L <: HList, N <: Nat, V]
    given tnBasic[T <: HList, V]: TakeNth[V :: T, _0, V] with {}
    given tnInductive[H, T <: HList, N <: Nat, V](using TakeNth[T, N, V]): TakeNth[H :: T, Succ[N], V] with {}

    // map column
    trait MapColumn[B <: Board, C <: Nat, O <: HList]
    // matrix of 1xn => a single value
    given mpBasic[R <: HList, C <: Nat, V](using TakeNth[R, C, V]): MapColumn[R :: HNil, C, V :: HNil] with {}
    // matrix of mxn => take first val from first row, mapColumn[(m-1)xn]
    given mpInductive[R <: HList, RT <: HList, C <: Nat, V, VT <: HList](
        using TakeNth[R, C, V], MapColumn[RT, C, VT]
    ): MapColumn[R :: RT, C, V :: VT] with {}

    trait WinsByColumnUpTo[B <: Board, C <: Nat, W <: Player]
    given winsFirstColumn[B <: Board, L <: HList, W <: Player](
      using MapColumn[B, _0, L], SameValues[L, W]
    ): WinsByColumnUpTo[B, _1, W] with {}
    given winsAnyColumn[B <: Board, C <: Nat, L <: HList, W <: Player](
      using MapColumn[B, C, L], SameValues[L, W]
    ): WinsByColumnUpTo[B, Succ[C], W] with {}
    given winsAnyColumn2[B <: Board, C <: Nat, W <: Player](
      using WinsByColumnUpTo[B, C, W]
    ): WinsByColumnUpTo[B, Succ[C], W] with {}

    trait WinsByColumn[B <: Board, W <: Player]
    given winsByAnyColumn[FR <: HList, RT <: HList, L <: Nat, W <: Player](
      using Length[FR, L], WinsByColumnUpTo[FR :: RT, L, W]
    ): WinsByColumn[FR :: RT, W] with {}

    // winner by diag 1
    trait Diag1[B <: Board, I <: Nat, D <: HList]
    given diag1Basic[R <: HList, N <: Nat, V](
      // length(r) == l, takeNth(r, l-1, v) => diag = [v]
      using Length[R, Succ[N]], TakeNth[R, N, V]
    ): Diag1[R :: HNil, N, V :: HNil] with {}
    given diag1Inductive[R <: HList, RT <: HList, N <: Nat, V, VT <: HList](
      using Diag1[RT, Succ[N], VT], TakeNth[R, N, V]
    ): Diag1[R :: RT, N, V :: VT] with {}

    trait WinsByDiag1[B <: Board, W <: Player]
    given wbd1[B <: Board, D1 <: HList, W <: Player](
      using Diag1[B, _0, D1], SameValues[D1, W]
    ): WinsByDiag1[B, W] with {}

    // winner by diag 2
    trait Diag2[B <: Board, I <: Nat, D <: HList]
    given diag2Basic[V, T <: HList]: Diag2[(V :: T) :: HNil, _0, V :: HNil] with {}
    given diag2Inductive[R <: HList, RT <: HList, I <: Nat, V, VT <: HList](
      using Diag2[RT, I, VT], TakeNth[R, Succ[I], V]
    ): Diag2[R :: RT, Succ[I], V :: VT] with {}

    trait WinsByDiag2[B <: Board, W <: Player]
    given wbd2[R <: HList, RT <: HList, N <: Nat, D2 <: HList, W <: Player](
      using Length[R, Succ[N]], Diag2[R :: RT, N, D2], SameValues[D2, W]
    ): WinsByDiag2[R :: RT, W] with {}

    trait Wins[B <: Board, W <: Player]
    given wbr[B <: Board, W <: Player](using WinsByRow[B, W]): Wins[B, W] with {}
    given wbc[B <: Board, W <: Player](using WinsByColumn[B, W]): Wins[B, W] with {}
    given d1[B <: Board, W <: Player](using WinsByDiag1[B, W]): Wins[B, W] with {}
    given d2[B <: Board, W <: Player](using WinsByDiag2[B, W]): Wins[B, W] with {}

    def printType[A](value: A)(using typename: TypeName[A]): String = typename.value

    def main(args: Array[String]): Unit = {
        val a = summon[Length[HNil, _0]]
        val b = summon[Length[EmptyBoard, _3]]

        val c = summon[WinsByRow[
          ("X" :: "X" :: "X" :: HNil) ::
          ("_" :: "_" :: "_" :: HNil) ::
          ("_" :: "_" :: "_" :: HNil) ::
          HNil,
          "X" ]]

        val d = summon[WinsByColumn[
          ("X" :: "_" :: "_" :: HNil) ::
          ("X" :: "_" :: "_" :: HNil) ::
          ("X" :: "_" :: "_" :: HNil) ::
          HNil,
          "X" ]]

        val e = summon[WinsByDiag1[
          ("X" :: "_" :: "_" :: HNil) ::
          ("_" :: "X" :: "_" :: HNil) ::
          ("_" :: "_" :: "X" :: HNil) ::
          HNil,
          "X" ]]

        val f = summon[WinsByDiag2[
          ("_" :: "_" :: "X" :: HNil) ::
          ("_" :: "X" :: "_" :: HNil) ::
          ("X" :: "_" :: "_" :: HNil) ::
          HNil,
          "X" ]]

        val winnerType = summon[Wins[
          ("_" :: "_" :: "X" :: HNil) ::
          ("_" :: "X" :: "_" :: HNil) ::
          ("X" :: "_" :: "_" :: HNil) ::
          HNil,
          "X" ]]

        println(printType(winnerType).replaceAll("TikTakToe", ""))
        // prints out which type has been used by Summon[] to determine a winner
    }
}
