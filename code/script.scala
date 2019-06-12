import scala.io.StdIn
import scala.io.Source

object Script {
  def main(args: Array[String]) {
    // var line: String = null
    // while({line = StdIn.readLine() ; line != null}) {
    //   println(line)
    // }
    println(Source.stdin.filterNot(_ == '\n').map(x => x.toString.toInt).fold(0)((x,y) => x+y))
  }
}
