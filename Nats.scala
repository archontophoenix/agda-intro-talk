object Nats {

  sealed trait Nat {
    def + (that: Nat): Nat = this match {
      case Z => that
      case S(n) => S(n + that)
    }
  }
  object Z extends Nat
  case class S (n: Nat) extends Nat

}
