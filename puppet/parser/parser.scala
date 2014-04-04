/* Parser using parser combinator in Scala */

import scala.util.parsing.combinator._
import scala.collection.immutable.List


class PuppetDSLParser extends RegexParsers with PackratParser {

  type P[T] = PackratParser[T]

  val expr: P[AST] = positioned (stmts_and_decls) | eof
  val stmts_and_decls: P[BlockExpr] = positioned (stmts_or_decls) | 
                                      positioned (stmt_and_decls) ~ positioned (stmt_or_decls) ^^ {
      case be => new BlockExpr ([be])
      case be~be' => be.push (be')
    }

  // TODO : See semantics
  val stmts: P[BlockExpr] = stmts_and_decls

  val stmts_or_decls: P[BlockExpr] = positioned (resource) |
                                     positioned (virtual_resource) |
                                     positioned (collection) |
                                     positioned (assignment) |
                                     positioned (casestmt) |
                                     positioned (ifstmt_begin) | 
                                     positioned (unlessstmt) |
                                     positioned (importstmt) | 
                                     positioned (fstmt) | 
                                     positioned (definition) |
                                     positioned (hostclass) |
                                     positioned (nodedef) |
                                     positioned (resourceoverride) |
                                     positioned (append) | 
                                     positioned (relationship)

  val relationship: P[Relationship] = positioned (relationship_side) ~ ("->" | "<-" | "~>" | "<~") ~ positioned (relationship_side) ^^ {
    case rs ~ "->" ~ rs => 
    case rs ~ "<-" ~ rs =>
    case rs ~ "~>" ~ rs =>
    case rs ~ "<~" ~ rs =>
  }
}




