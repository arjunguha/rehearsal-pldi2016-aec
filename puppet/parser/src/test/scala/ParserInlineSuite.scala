import org.scalatest.FunSpec
import org.scalatest.Matchers
import puppet._


class ParserInlineSpec extends FunSpec with Matchers {

  describe ("When parsing append operator") {

    it ("should not raise syntax errors") {
      PuppetParser ("$var += something")
    }

    it ("should raise syntax errors on incomplete syntax") {
      intercept [PuppetParserException] {
      PuppetParser ("$var += ")
      }
    }

    it ("should create ast::VarDef with append=true") {
      PuppetParser ("$var += 2") match {
        case BlockStmtDecls (List (Vardef (_, _, append))) => append should be (true)
        case _ => fail ("Expected Vardef")
      }
    }

    it ("should work with arrays too") {
      PuppetParser ("$var += ['test']") match {
        case BlockStmtDecls (List (Vardef (_, ASTArray (_), append))) => append should be (true)
        case _ => fail ("Expected Vardef")
      }
    }
  }

  describe ("when parsing selector") {
    it ("should support hash access on the left hand side") {
      PuppetParser ("$h = { 'a' => 'b' } $a = $h['a'] ? { 'b' => 'd', default => undef }")
    }
  }


  describe ("parsing 'unless'") {
    it ("should create the correct ast objects") {
      PuppetParser ("unless false { $var = 1 }") match {
        case BlockStmtDecls (List (IfExpr (NotExpr (x), _, _))) => x shouldBe a [ASTBool]
        case _ => fail ("Expected NotExpr")
      }
    }

    it ("should not raise an error with empty statements") {
      PuppetParser ("unless false { }")
    }

    // test for bug #13296
    it ("should not override 'unless' as a parameter inside resources") {
      PuppetParser ("exec {'/bin/echo foo': unless => '/usr/bin/false',}")
    }
  }

  describe ("when parsing parameter names") {
    PuppetParser.lexical.reserved.foreach (keyword => 
        it ("should allow " + keyword + " as a keyword") {
          PuppetParser ("exec {'/bin/echo foo': " + keyword + "  => '/usr/bin/false',}")
      })
    }

  describe ("when parsing 'if'") {
    it ("not, it should create the correct ast objects") {
      PuppetParser ("if ! true { $var = 1 }") match {
        case BlockStmtDecls (List (IfExpr (NotExpr (x), _, _))) => x shouldBe a [ASTBool]
        case _ => fail ("Expected NotExpr")
      }
    }

    it ("boolean operation, it should create the correct ast objects") {
      PuppetParser ("if true or true { $var = 1 }") match {
        case BlockStmtDecls (List (IfExpr (BinExpr (lhs, rhs, op), _, _))) => {
          lhs shouldBe a [ASTBool]
          rhs shouldBe a [ASTBool]
          op should be (Or)
        }
        case _ => fail ("Expected BinaryExpression")
      }
    }

    it ("comparison operation, it should create the correct ast objects") {
      PuppetParser ("if 1 < 2 { $var = 1 }") match {
        case BlockStmtDecls (List (IfExpr (BinExpr (lhs, rhs, op), _, _))) => 
          lhs shouldBe a [Name]
          rhs shouldBe a [Name]
          op should be (LessThan)
        case _ => fail ("Expected BinaryExpression")
      }
    }
  }

  describe ("when parsing if complex expressions") {

    it ("should create a correct ast tree") {
      PuppetParser ("if (1 > 2) and (1 == 2) { $var = 1 }") match {
        case BlockStmtDecls (List (IfExpr (BinExpr (lhs, rhs, op), _, _))) => 
          op should be (And)
          lhs match {
            case BinExpr (lhs, rhs, op) =>
              lhs shouldBe a [Name]
              rhs shouldBe a [Name]
              op should be (GreaterThan)
            case _ => fail ("Expected Binary Expression for lhs")
          }
          rhs match {
            case BinExpr (lhs, rhs, op) =>
              lhs shouldBe a [Name]
              rhs shouldBe a [Name]
              op should be (Equal)
            case _ => fail ("Expected Binary Expression for rhs")
          }
        case _ => fail ("Expected Binary Expression for if condition")
      }
    }

    it ("should raise an error on incorrect expression") {
      intercept [PuppetParserException] {
        PuppetParser ("if (1 > 2 > ) or (1 == 2) { $var = 1 }")
      }
    }
  }

  describe ("when parsing resource references") {

    it ("should not raise syntax errors") {
      PuppetParser ("exec { test: param => File[\"a\"] }")
    }

    it ("should not raise syntax errors with multiple references") {
      PuppetParser ("exec { test: param => File[\"a\",\"b\"] }")
    }
  }

  describe ("when parsing resource overrides") {

    it ("should not raise syntax errors") {
      PuppetParser ("Resource[\"title\"] { param => value }")
    }

    it ("should not raise syntax errors with multiple overrides") {
      PuppetParser ("Resource[\"title1\",\"title2\"] { param => value }")
    }

    it ("should create an ast::ResourceOverride") {
      PuppetParser ("Resource[\"title1\",\"title2\"] { param => value }") match {
        case BlockStmtDecls (List (ResourceOverride (ref, resparams))) =>
          ref shouldBe a [ResourceRef]
          resparams shouldBe a [List[Attribute]]
        case _ => fail ("Expected ResourceOverride")
      }
    }
  }

  describe ("when parsing if statements") {

    it ("should not raise errors with empty if") {
       PuppetParser ("if true { }") 
    }

    it ("should not raise errors with empty else") {
       PuppetParser ("if false { notice('if') } else { }") 
    }

    it ("should not raise errors with empty if and else") {
       PuppetParser ("if false { } else { }") 
    }

    it ("should build a chain of 'ifs' if there's an 'elsif'") {
      PuppetParser ("if true { notice('test') } elsif true {} else { }")
    }
  }

  describe ("when parsing function calls") {
    it ("should not raise errors with no arguments") {
       PuppetParser ("tag()") 
    }

    it ("should not raise errors with rvalue function with no args") {
       PuppetParser ("$a = template()") 
    }

    it ("should not raise errors with arguments") {
       PuppetParser ("notice(1)") 
    }

    it ("should not raise errors with multiple arguments") {
       PuppetParser ("notice(1,2)") 
    }

    it ("should not raise errors with multiple arguments and a trailing comma") {
       PuppetParser ("notice(1,2,)") 
    }

    it ("should signal an error parsing function applications with two args and no commas") {
      intercept [PuppetParserException] {
        PuppetParser("foo foo foo")
      }
    }

    it ("should parse a function application without parentheses") {
      PuppetParser("foo foo")
    }

    it ("should parse two function applications without parentheses") {
      // This is awful.
      PuppetParser("foo foo foo foo")
    }

  }

  describe ("when parsing arrays") {
    it ("should parse an array") {
       PuppetParser ("$a = [1,2]") 
    }

    it ("should not raise errors with a trailing comma") {
       PuppetParser ("$a = [1,2,]") 
    }

    it ("should accept an empty array") {
       PuppetParser ("$var = []\n") 
    }
  }

  describe ("when parsing classes") {

    it ("should not create new classes") {
      PuppetParser ("class foobar {}") match {
        case BlockStmtDecls (List (Hostclass (name , _, _, _))) => name should be ("foobar")
        case _ => fail ("Expected Hostclass")
      }
    }

    it ("should correctly set the parent class when one is provided") {
      PuppetParser ("class foobar inherits yayness {}") match {
        case BlockStmtDecls (List (Hostclass (_, _, Some (parent), _))) => parent should be ("yayness")
        case _ => fail ("Exptected parent")
      }
    }

    it ("should correctly set the parent class for multiple classes at a time") {
      PuppetParser ("class foobar inherits yayness {}\nclass boo inherits bar {}") match {
        case BlockStmtDecls (List (Hostclass (_, _, Some (parent1), _), Hostclass (_, _, Some (parent2), _))) =>
          parent1 should be ("yayness")
          parent2 should be ("bar")
        case _ => fail ("Expected parents")
      }
    }

    it ("should define the code when some is provided") {
      PuppetParser ("class foobar { $var = val }") match {
        case BlockStmtDecls (List (Hostclass (_, _, _, stmts))) => stmts should not be (Nil)
        case _ => fail ("Exptected statements")
      }
    }
  }

  describe ("when parsing resources") {

    it ("should be able to parse class resources") {
       PuppetParser ("class { foobar: biz => stuff }") match {
         case BlockStmtDecls (List (Resource (_, List (ResourceInstance (Name (name), _))))) => 
           name should be ("foobar")
         case _ => fail ("Exptected a Resource")
       }
    }

    it ("should correctly mark exported resources as exported") {
      PuppetParser ("@@file { '/file': }") match {
        case BlockStmtDecls (List (VirtualResource (_, x))) => x should be (Vrtexported)
        case _ => fail ("Expected a virtual resource")
      }
    }

    it ("should correctly mark virtual resources as virtual") {
      PuppetParser ("@file { '/file': }") match {
        case BlockStmtDecls (List (VirtualResource (_, x))) => x should be (Vrtvirtual)
        case _ => fail ("Expected a virtual resource")
      }
    }
  }

  describe ("when parsing nodes") {

    it ("should be able to parse a node with a single name") {
      PuppetParser ("node foo { }") match {
        case BlockStmtDecls (List (Node (hostnames, _, _))) => 
          hostnames.length should be (1)
          (hostnames.head match {
             case Name (value) => value
             case _ => fail ("Expected Name")
           }) should be ("foo")
        case _ => fail ("Expected Node")
      }
    }

    it ("should be able to parse a node with three names") {
      PuppetParser ("node foo, bar, baz { }") match {
        case BlockStmtDecls (List (Node (hostnames, _, _))) => 
          hostnames.length should be (3)
          (hostnames.head match {
            case Name (value) => value
            case _ => fail ("Expected Name")
          }) should be ("foo")
          (hostnames.tail.head match {
             case Name (value) => value
             case _ => fail ("Expected Name")
          }) should be ("bar")
          (hostnames.tail.tail.head match {
             case Name (value) => value
             case _ => fail ("Expected Name")
          }) should be ("baz")
        case _ => fail ("Expected Node")
      }
    }
  }

  describe ("when parsing collections") {
    it ("should parse basic collections") {
      PuppetParser ("Port <| |>") match {
        case BlockStmtDecls (List (x)) =>
          x shouldBe a [Collection]
        case _ => fail ("Expected Collection")
      }
    }

    it ("should parse fully qualified collections") {
      PuppetParser ("Port::Range <| |>") match {
        case BlockStmtDecls (List (x)) => x shouldBe a [Collection]
        case _ => fail ("Expected Collection")
      }
    }
  }

  /*
  it ("should not assign to a fully qualified variable") {
    expect {
      PuppetParser ("$one::two = yay")
    }.to raise_error(Puppet::ParseError, /Cannot assign to variables in other namespaces/)
  }
  */

  it ("should parse assignment of undef") {
    PuppetParser ("$var = undef") match {
      case BlockStmtDecls (List (Vardef (_, x, _))) => x should be (Undef)
      case _ => fail ("Expected Vardef")
    }
  }

  /*
  context "#namesplit" {
    { "base::sub" => %w{base sub},
      "main" => ["", "main"],
      "one::two::three::four" => ["one::two::three", "four"],
    }.each { |input, output|
      it ("should split #{input.inspect} to #{output.inspect}") {
        @parser.namesplit(input).should == output
      }
    }
  }

  it ("should treat classes as case insensitive") {
    @parser.known_resource_types.import_ast(PuppetParser ("class yayness {}"), '')
    @parser.known_resource_types.hostclass('yayness').
      should == @parser.find_hostclass("", "YayNess")
  }

  it ("should treat defines as case insensitive") {
    @parser.known_resource_types.import_ast(PuppetParser ("define funtest {}"), '')
    @parser.known_resource_types.hostclass('funtest').
      should == @parser.find_hostclass("", "fUntEst")
  }
  */
}
