import scala.util.parsing.combinator._

class EBNF extends RegexParsers {
  def nonterminal: Parser[String] = """<[^>]+>""".r ^^ { _.toString }
  def rule_delim: Parser[Any] = """::=""" ^^ { _.toString }
  def rhs: Parser[String] = """.*""".r ^^ { _.toString }
  def rule: Parser[(String, String)] = nonterminal ~ rule_delim ~ rhs ^^ { case nt ~ _ ~ rh => (nt, rh) }
  def root: Parser[List[(String, String)]] = rep(rule)

  def apply(grammar: String) = parseAll(root, grammar) match {
    case Success(result, _) => result
    case failure: NoSuccess => scala.sys.error(failure.msg)
  }

  def ws = whiteSpace // === """\s+""".r
}

object EBNF extends EBNF {
  def main(args: Array[String]) {
    args foreach println _
    args.map(EBNF(_)).foreach { println(_) }
  }
}
