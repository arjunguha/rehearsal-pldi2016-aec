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
      val vardef = PuppetParser ("$var += 2")
      vardef should be (BlockExpr (List (Vardef (Name ("$var"), Name ("2"), true))))
    }

    it ("should work with arrays too") {
      val vardef = PuppetParser ("$var += ['test']")
      vardef shouldBe a [Vardef]
      // vardef.append should be (true)
    }
  }

  describe ("when parsing selector") {
    it ("should support hash access on the left hand side") {
      PuppetParser ("$h = { 'a' => 'b' } $a = $h['a'] ? { 'b' => 'd', default => undef }")
    }
  }

  describe ("parsing 'unless'") {
    it ("should create the correct ast objects") {
      val ast = PuppetParser ("unless false { $var = 1 }")
      ast shouldBe a [Vardef]
      // Puppet::Parser::AST::Not.expects(:new).with { |h| h[:value].is_a?(Puppet::Parser::AST::Boolean) }
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

  /*
  describe ("when parsing 'if'") {
    it ("not, it should create the correct ast objects") {
      Puppet::Parser::AST::Not.expects(:new).with { |h| h[:value].is_a?(Puppet::Parser::AST::Boolean) }
      PuppetParser ("if ! true { $var = 1 }")
    }

    it ("boolean operation, it should create the correct ast objects") {
      Puppet::Parser::AST::BooleanOperator.expects(:new).with {
        |h| h[:rval].is_a?(Puppet::Parser::AST::Boolean) and h[:lval].is_a?(Puppet::Parser::AST::Boolean) and h[:operator]=="or"
      }
      PuppetParser ("if true or true { $var = 1 }")

    }

    it ("comparison operation, it should create the correct ast objects") {
      Puppet::Parser::AST::ComparisonOperator.expects(:new).with {
        |h| h[:lval].is_a?(Puppet::Parser::AST::Name) and h[:rval].is_a?(Puppet::Parser::AST::Name) and h[:operator]=="<"
      }
      PuppetParser ("if 1 < 2 { $var = 1 }")

    }
  }
  */

  describe ("when parsing if complex expressions") {

  /*
    it ("should create a correct ast tree") {
      aststub = stub_everything 'ast'
      Puppet::Parser::AST::ComparisonOperator.expects(:new).with {
        |h| h[:rval].is_a?(Puppet::Parser::AST::Name) and h[:lval].is_a?(Puppet::Parser::AST::Name) and h[:operator]==">"
      }.returns(aststub)
      Puppet::Parser::AST::ComparisonOperator.expects(:new).with {
        |h| h[:rval].is_a?(Puppet::Parser::AST::Name) and h[:lval].is_a?(Puppet::Parser::AST::Name) and h[:operator]=="=="
      }.returns(aststub)
      Puppet::Parser::AST::BooleanOperator.expects(:new).with {
        |h| h[:rval]==aststub and h[:lval]==aststub and h[:operator]=="and"
      }
      PuppetParser ("if (1 > 2) and (1 == 2) { $var = 1 }")
    }
    */

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

    /*
    it ("should create an ast::ResourceReference") {
      Puppet::Parser::AST::ResourceReference.expects(:new).with { |arg|
        arg[:line]==1 and arg[:type]=="File" and arg[:title].is_a?(Puppet::Parser::AST::ASTArray)
      }
      @parser.parse('exec { test: command => File["a","b"] }')
    }
    */
  }

  describe ("when parsing resource overrides") {

    it ("should not raise syntax errors") {
      PuppetParser ("Resource[\"title\"] { param => value }")
    }

    it ("should not raise syntax errors with multiple overrides") {
      PuppetParser ("Resource[\"title1\",\"title2\"] { param => value }")
    }

  /*
    it ("should create an ast::ResourceOverride") {
      #Puppet::Parser::AST::ResourceOverride.expects(:new).with { |arg|
      #  arg[:line]==1 and arg[:object].is_a?(Puppet::Parser::AST::ResourceReference) and arg[:parameters].is_a?(Puppet::Parser::AST::ResourceParam)
      #}
      ro = @parser.parse('Resource["title1","title2"] { param => value }').code[0]
      ro.should be_a(Puppet::Parser::AST::ResourceOverride)
      ro.line.should == 1
      ro.object.should be_a(Puppet::Parser::AST::ResourceReference)
      ro.parameters[0].should be_a(Puppet::Parser::AST::ResourceParam)
    }
  */
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

  /*
    it ("should create a nop node for empty branch") {
      Puppet::Parser::AST::Nop.expects(:new)
      PuppetParser ("if true { }")
    }

    it ("should create a nop node for empty else branch") {
      Puppet::Parser::AST::Nop.expects(:new)
      PuppetParser ("if true { notice('test') } else { }")
    }

    it ("should build a chain of 'ifs' if there's an 'elsif'") {
      expect { @parser.parse(<<-PP) }.to_not raise_error
        if true { notice('test') } elsif true {} else { }
      PP
    }
    */

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

  /*
  describe ("when building ast nodes") {
    before {
      @lexer = stub 'lexer', :line => 50, :file => "/foo/bar", :getcomment => "whev"
      @parser.stubs(:lexer).returns @lexer
      @class = Puppet::Resource::Type.new(:hostclass, "myclass", :use_docs => false)
    }

    it ("should return a new instance of the provided class created with the provided options") {
      @class.expects(:new).with { |opts| opts[:foo] == "bar" }
      @parser.ast(@class, :foo => "bar")
    }

    it ("should merge the ast context into the provided options") {
      @class.expects(:new).with { |opts| opts[:file] == "/foo" }
      @parser.expects(:ast_context).returns :file => "/foo"
      @parser.ast(@class, :foo => "bar")
    }

    it ("should prefer provided options over AST context") {
      @class.expects(:new).with { |opts| opts[:file] == "/bar" }
      @lexer.expects(:file).returns "/foo"
      @parser.ast(@class, :file => "/bar")
    }
  }

  describe ("when parsing classes") {
    before :each {
      @krt = Puppet::Resource::TypeCollection.new("development")
      @parser = Puppet::Parser::Parser.new "development"
      @parser.stubs(:known_resource_types).returns @krt
    }

    it ("should not create new classes") {
      PuppetParser ("class foobar {}").code[0].should be_a(Puppet::Parser::AST::Hostclass)
      @krt.hostclass("foobar").should be_nil
    }

    it ("should correctly set the parent class when one is provided") {
      PuppetParser ("class foobar inherits yayness {}").code[0].instantiate('')[0].parent.should == "yayness"
    }

    it ("should correctly set the parent class for multiple classes at a time") {
      statements = PuppetParser ("class foobar inherits yayness {}\nclass boo inherits bar {}").code
      statements[0].instantiate('')[0].parent.should == "yayness"
      statements[1].instantiate('')[0].parent.should == "bar"
    }

    it ("should define the code when some is provided") {
      PuppetParser ("class foobar { $var = val }").code[0].code.should_not be_nil
    }

    it ("should accept parameters with trailing comma") {
      PuppetParser ("file { '/example': ensure => file, }").should be
    }

    it ("should accept parametrized classes with trailing comma") {
      PuppetParser ("class foobar ($var1 = 0,) { $var = val }").code[0].code.should_not be_nil
    }

    it ("should define parameters when provided") {
      foobar = PuppetParser ("class foobar($biz,$baz) {}").code[0].instantiate('')[0]
      foobar.arguments.should == {"biz" => nil, "baz" => nil}
    }
  }

  describe ("when parsing resources") {
    before :each {
      @krt = Puppet::Resource::TypeCollection.new("development")
      @parser = Puppet::Parser::Parser.new "development"
      @parser.stubs(:known_resource_types).returns @krt
    }

    it ("should be able to parse class resources") {
      @krt.add(Puppet::Resource::Type.new(:hostclass, "foobar", :arguments => {"biz" => nil}))
       PuppetParser ("class { foobar: biz => stuff }") 
    }

    it ("should correctly mark exported resources as exported") {
      PuppetParser ("@@file { '/file': }").code[0].exported.should be_true
    }

    it ("should correctly mark virtual resources as virtual") {
      PuppetParser ("@file { '/file': }").code[0].virtual.should be_true
    }
  }

  describe ("when parsing nodes") {
    it ("should be able to parse a node with a single name") {
      node = PuppetParser ("node foo { }").code[0]
      node.should be_a Puppet::Parser::AST::Node
      node.names.length.should == 1
      node.names[0].value.should == "foo"
    }

    it ("should be able to parse a node with two names") {
      node = PuppetParser ("node foo, bar { }").code[0]
      node.should be_a Puppet::Parser::AST::Node
      node.names.length.should == 2
      node.names[0].value.should == "foo"
      node.names[1].value.should == "bar"
    }

    it ("should be able to parse a node with three names") {
      node = PuppetParser ("node foo, bar, baz { }").code[0]
      node.should be_a Puppet::Parser::AST::Node
      node.names.length.should == 3
      node.names[0].value.should == "foo"
      node.names[1].value.should == "bar"
      node.names[2].value.should == "baz"
    }
  }

  it ("should fail if trying to collect defaults") {
    expect {
      PuppetParser ("@Port { protocols => tcp }")
    }.to raise_error(Puppet::ParseError, /Defaults are not virtualizable/)
  }

  context "when parsing collections" {
    it ("should parse basic collections") {
      PuppetParser ("Port <| |>").code.
        should be_all {|x| x.is_a? Puppet::Parser::AST::Collection }
    }

    it ("should parse fully qualified collections") {
      PuppetParser ("Port::Range <| |>").code.
        should be_all {|x| x.is_a? Puppet::Parser::AST::Collection }
    }
  }

  it ("should not assign to a fully qualified variable") {
    expect {
      PuppetParser ("$one::two = yay")
    }.to raise_error(Puppet::ParseError, /Cannot assign to variables in other namespaces/)
  }

  it ("should parse assignment of undef") {
    tree = PuppetParser ("$var = undef")
    tree.code.children[0].should be_an_instance_of Puppet::Parser::AST::VarDef
    tree.code.children[0].value.should be_an_instance_of Puppet::Parser::AST::Undef
  }

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
}
  }
  */
}
