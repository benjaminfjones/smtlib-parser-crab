extern crate peg;

#[allow(dead_code)]
const RESERVED_WORDS: [&str; 13] = [
    "BINARY",
    "DECIMAL",
    "HEXADECIMAL",
    "NUMERAL",
    "STRING",
    "_",
    "!",
    "as",
    "let",
    "exists",
    "forall",
    "match",
    "par",
    // TODO: add script commands
];

peg::parser! {
    pub grammar smtlib_parser() for str {
        rule whitespace_char() = quiet!{[' ' | '\t' | '\n' | '\r']}
        rule _() = quiet!{whitespace_char()*}   // optional whitespace
        rule __() = quiet!{whitespace_char()+}  // required whitespace
        // http://www.unicode.org/glossary/#unicode_scalar_value
        rule printable_char() -> &'input str
            = $(['\u{0020}'..='\u{007E}' | '\u{0080}'..='\u{D7FF}' | '\u{E000}'..='\u{10FFFF}'])
        rule printable_non_quote() -> &'input str
            = $(['\u{0020}'..='\u{0021}' | '\u{0023}'..='\u{007E}' | '\u{0080}'..='\u{D7FF}' | '\u{E000}'..='\u{10FFFF}'])
        rule quoted_symbol_char() -> &'input str
            = $(!['|' | '\u{005c}'] (whitespace_char() / printable_char()))
        rule digit() -> &'input str
            = $(['0'..='9'])
        rule letter() -> &'input str
            = $(['a'..='z' | 'A'..='Z'])
        rule symbol_char() -> &'input str
            = $(['~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' |
                '.' | '?' | '/'])
        // an escaped quote inside a string literal
        rule esc_quote() -> &'input str
            = $("\"\"")
        pub rule numeral() -> &'input str
            = n:$(['0']) !digit() {n} / n:$(['1'..='9']['0'..='9']*) !"." {n}
        pub rule decimal() -> &'input str
            = $(("0" / ['1'..='9']['0'..='9']*) "." ['0'..='1']+)
        pub rule hexadecimal() -> &'input str
            = $("#x" ['0'..='9' | 'a'..='f' | 'A'..='F']+)
        pub rule binary() -> &'input str
            = $("#b" ['0'..='1']+)
        pub rule string() -> &'input str
            = $("\"" (esc_quote() / printable_non_quote() / whitespace_char())* "\"")
        // validation: simple_symbol also must not start w/ a digit or be a reserved word. Also,
        // symbols that start with @ or . are reserved for solver internal use.
        rule simple_symbol() -> &'input str
            = $((letter() / digit() / symbol_char())+)
        // any sequence of whitespace or printable chars (except | and \), enclosed in vertical bars
        // this production returns only what's inside the bars
        rule quoted_symbol() -> &'input str
            = "|" qs:$(quoted_symbol_char()*) "|" { qs }
        pub rule raw_symbol() -> &'input str
            = simple_symbol() / quoted_symbol()
        pub rule keyword() -> &'input str
            = $(":" simple_symbol())

        // S-expressions
        rule spec_constant() -> &'input str
            = $(numeral() / decimal() / hexadecimal() / binary() / string())
        pub rule s_expr() -> &'input str
            = $(spec_constant() / raw_symbol() / keyword() / "(" _ (s_expr() ** __) _ ")")

        // identifiers
        rule index() -> &'input str
            = $(numeral() / raw_symbol())
        pub rule identifier() -> &'input str
            = $(raw_symbol() / "(" _ "_" _ (index() **<1,> __) _ ")")

        // attributes
        // TODO: parse attribute values
        rule attribute_value() -> &'input str
            = $(spec_constant() / raw_symbol() / "(" _ (s_expr() ** __) _ ")")
        pub rule attribute() -> Attribute
            = k:keyword() { Attribute(Keyword(k.to_string()), None) }
            / k:keyword() __ v:attribute_value()
                { Attribute(Keyword(k.to_string()), Some(v.to_string())) }

        // terms and formulas
        //
        // Note: the productions below here generally result in AST values, not input strings
        //
        // <qual_identifier> ::= <identifier> | ( as <identifier> <sort> )
        // <var_binding> ::= ( <symbol> <term> )
        // <sorted_var> ::= ( <symbol> <sort> )
        // <pattern> ::= <symbol> | ( <symbol> <symbol + )
        // <match_case> ::= ( <pattern> <term> )
        // <term> ::= <spec_constant>
        //          | <qual_identifier>
        //          | ( <qual_identifier> <term>+ )
        //          | ( let ( <var_binding>+ ) <term> )
        //          | ( forall ( <sorted_var>+ ) <term> )
        //          | ( exists ( <sorted_var>+ ) <term> )
        //          | ( match <term> ( <match_case>+ ) )
        //          | ( ! <term> <attribute>+ )
        //
        pub rule sort() -> Sort
            = i:identifier() { Sort(i.to_string(), Vec::new()) }
            / "(" _ i:identifier() __ ss:(sort() **<1,> __) _ ")" { Sort(i.to_string(), ss) }
        rule qual_identifier() -> QualIdentifier
            = i:identifier() { QualIdentifier(i.to_string(), None) }
            / "(" _ "as" __ i:identifier() __ s:sort() _ ")" { QualIdentifier(i.to_string(), Some(s)) }
        pub rule symbol() -> Symbol
            = s:raw_symbol() { Symbol(s.to_string()) }
        rule var_binding() -> VarBinding
            = "(" _ s:symbol() __ t:term() _ ")" { VarBinding(s, t) }
        rule sorted_var() -> SortedVar
            = "(" _ s:symbol() __ sort:sort() _ ")" { SortedVar(s, sort) }
        rule pattern() -> Pattern
            = s:symbol() { Pattern(s, Vec::new()) }
            / "(" _ s:symbol() __ ss:(symbol() **<1,> __) _ ")" { Pattern(s, ss) }
        rule match_case() -> MatchCase
            = "(" _ p:pattern() __ t:term() _ ")" { MatchCase(p, t) }
        pub rule term() -> Term
            = s:spec_constant() { Term::SpecConstant(s.to_string()) }
            / qi:qual_identifier() { Term::QualIdentifier(qi) }
            / "(" _ "let" __ "(" vbs:(var_binding() **<1,> _) _ ")" __ t:term() _ ")" { Term::Let(vbs, Box::new(t)) }
            / "(" _ "forall" __ "(" svs:(sorted_var() **<1,> __) _ ")" __ t:term() _ ")" { Term::Forall(svs, Box::new(t)) }
            / "(" _ "exists" __ "(" svs:(sorted_var() **<1,> __) _ ")" __ t:term() _ ")" { Term::Exists(svs, Box::new(t)) }
            / "(" _ "match" __ t:term() __ "(" _ mcs:(match_case() **<1,> __) _ ")" _ ")" { Term::Match(Box::new(t), mcs) }
            / "(" _ "!" __ t:term() __ attrs:(attribute() **<1,> __) _ ")" { Term::Bang(Box::new(t), attrs) }
            / "(" _ qi:qual_identifier() __ ts:(term() **<1,> __) _ ")" { Term::App(qi, ts) }
    }
}

// newtypes for use in Term
#[derive(Debug, Eq, PartialEq)]
pub struct Symbol(String);
#[derive(Debug, Eq, PartialEq)]
pub struct Sort(String, Vec<Sort>);
#[derive(Debug, Eq, PartialEq)]
pub struct QualIdentifier(String, Option<Sort>); // identifier name, sort
#[derive(Debug, Eq, PartialEq)]
pub struct VarBinding(Symbol, Term);
#[derive(Debug, Eq, PartialEq)]
pub struct SortedVar(Symbol, Sort);
#[derive(Debug, Eq, PartialEq)]
pub struct Pattern(Symbol, Vec<Symbol>);
#[derive(Debug, Eq, PartialEq)]
pub struct MatchCase(Pattern, Term);
#[derive(Debug, Eq, PartialEq)]
pub struct Keyword(String);
#[derive(Debug, Eq, PartialEq)]
pub struct Attribute(Keyword, Option<String>);

#[derive(Debug, Eq, PartialEq)]
pub enum Term {
    /// Constant
    SpecConstant(String),
    /// Bare identifier
    QualIdentifier(QualIdentifier),
    /// Function application
    App(QualIdentifier, Vec<Term>),
    /// Let binding
    Let(Vec<VarBinding>, Box<Term>),
    /// Universal quantifier
    Forall(Vec<SortedVar>, Box<Term>),
    /// Existential quantifier
    Exists(Vec<SortedVar>, Box<Term>),
    /// Match for algebraic datatypes (rare in QF_LIA)
    Match(Box<Term>, Vec<MatchCase>),
    /// Annotated Term (rare in QF_LIA)
    Bang(Box<Term>, Vec<Attribute>),
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_numeral() {
        assert_eq!(smtlib_parser::numeral("1"), Ok("1"));
        assert_eq!(smtlib_parser::numeral("0"), Ok("0"));
        assert_eq!(smtlib_parser::numeral("101"), Ok("101"));
        assert!(smtlib_parser::numeral("01").is_err());
        assert!(smtlib_parser::numeral("01a").is_err());
    }

    #[test]
    fn test_decimal() {
        assert_eq!(smtlib_parser::decimal("1.0"), Ok("1.0"));
        assert_eq!(smtlib_parser::decimal("1.1"), Ok("1.1"));
        assert_eq!(smtlib_parser::decimal("0.000"), Ok("0.000"));
        assert_eq!(smtlib_parser::decimal("1.000"), Ok("1.000"));
        assert_eq!(smtlib_parser::decimal("0.001"), Ok("0.001"));
        assert_eq!(smtlib_parser::decimal("10.0010"), Ok("10.0010"));
        assert!(smtlib_parser::decimal("0.").is_err());
        assert!(smtlib_parser::decimal("0").is_err());
        assert!(smtlib_parser::decimal("10").is_err());
        assert!(smtlib_parser::decimal("0f").is_err());
    }

    #[test]
    fn test_hexadecimal() {
        assert_eq!(smtlib_parser::hexadecimal("#xdeadbeef"), Ok("#xdeadbeef"));
        assert_eq!(smtlib_parser::hexadecimal("#xDEADbeef"), Ok("#xDEADbeef"));
        assert_eq!(smtlib_parser::hexadecimal("#x0f"), Ok("#x0f"));
        assert!(smtlib_parser::hexadecimal("#x").is_err());
        assert!(smtlib_parser::hexadecimal("#x1R").is_err());
        assert!(smtlib_parser::hexadecimal("#x 00F").is_err());
    }

    #[test]
    fn test_binary() {
        assert_eq!(smtlib_parser::binary("#b1010"), Ok("#b1010"));
        assert_eq!(smtlib_parser::binary("#b010"), Ok("#b010"));
        assert_eq!(smtlib_parser::binary("#b0"), Ok("#b0"));
        assert!(smtlib_parser::binary("#b").is_err());
        assert!(smtlib_parser::binary("#b1R").is_err());
        assert!(smtlib_parser::binary("#b 001").is_err());
    }

    #[test]
    fn test_string() {
        assert_eq!(smtlib_parser::string("\"hello\""), Ok("\"hello\""));
        assert_eq!(
            smtlib_parser::string("\"hello world\""),
            Ok("\"hello world\"")
        );
        assert_eq!(
            smtlib_parser::string("\"she said \"\"hello world\"\"\""),
            Ok("\"she said \"\"hello world\"\"\"")
        );
        let multi_line = r#""this is a string literal
        with a line break in it""#;
        assert_eq!(smtlib_parser::string(multi_line), Ok(multi_line));
        assert!(smtlib_parser::string("\"bad \"news\"").is_err())
    }

    #[test]
    fn test_symbol() {
        assert_eq!(smtlib_parser::raw_symbol("|symbol|"), Ok("symbol"));
        assert!(smtlib_parser::raw_symbol("FOOBAR").is_ok());
        assert!(smtlib_parser::raw_symbol("!foo").is_ok());
        assert!(smtlib_parser::raw_symbol("~~~").is_ok());
        assert!(smtlib_parser::raw_symbol("foo01").is_ok());
        assert!(smtlib_parser::raw_symbol("BINARY").is_ok()); // parses OK, but shouldn't validate
        assert!(smtlib_parser::raw_symbol("1.0").is_ok()); // parses OK, but doesn't validate
        assert!(smtlib_parser::raw_symbol("0foo").is_ok()); // parses OK, but doesn't validate
        assert!(smtlib_parser::raw_symbol("|foo\"bar|").is_ok());
        assert!(smtlib_parser::raw_symbol("||").is_ok());
        assert!(
            smtlib_parser::raw_symbol(r#"|af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ’]]984|"#).is_ok()
        );

        assert_eq!(smtlib_parser::symbol("foo"), Ok(Symbol("foo".to_string())));
        // quoted symbols parse into the value inside the quotes
        assert_eq!(
            smtlib_parser::symbol("|foo|"),
            Ok(Symbol("foo".to_string()))
        );

        let multi_line = r#"|this is a symbol
        with a line break in it|"#;
        assert!(smtlib_parser::raw_symbol(multi_line).is_ok());

        // negative parses
        assert!(smtlib_parser::raw_symbol("|sym|ol|").is_err());
        assert!(smtlib_parser::raw_symbol(r#"|sym\ol|"#).is_err());
    }

    #[test]
    fn test_keyword() {
        assert!(smtlib_parser::keyword(":symbol").is_ok());
        assert!(smtlib_parser::keyword(":FOOBAR").is_ok());
        assert!(smtlib_parser::keyword(":!").is_ok());

        assert!(smtlib_parser::keyword("foo").is_err());
        assert!(smtlib_parser::keyword(":|").is_err());
        assert!(smtlib_parser::keyword(":|").is_err());
    }

    #[test]
    fn test_s_expr() {
        assert!(smtlib_parser::s_expr("123").is_ok());
        assert!(smtlib_parser::s_expr("1.0").is_ok());
        assert!(smtlib_parser::s_expr("#x123").is_ok());
        assert!(smtlib_parser::s_expr("#x101").is_ok());
        assert!(smtlib_parser::s_expr("\"hello\"").is_ok());
        assert!(smtlib_parser::s_expr(":keyword").is_ok());
        assert!(smtlib_parser::s_expr("!symbol").is_ok());
        assert!(smtlib_parser::s_expr("|symbol|").is_ok());
        assert!(smtlib_parser::s_expr("(symbol)").is_ok());
        assert!(smtlib_parser::s_expr("()").is_ok());
        assert!(smtlib_parser::s_expr("( )").is_ok());
        assert!(smtlib_parser::s_expr("(())").is_ok());
        assert!(smtlib_parser::s_expr("(\"symbol\")").is_ok());
        assert!(smtlib_parser::s_expr("(+ 1 x)").is_ok());
        assert!(smtlib_parser::s_expr("(+ 1 (+ 1 x))").is_ok());
        assert!(smtlib_parser::s_expr("((hello)  (world) )").is_ok());
        assert!(smtlib_parser::s_expr("(match (+ 1 x) ((y (+ 1 y))))").is_ok());

        assert!(smtlib_parser::s_expr("(+ 1 x").is_err());
        assert!(smtlib_parser::s_expr("(+ 1 x))").is_err());
        assert!(smtlib_parser::s_expr("((())").is_err());
    }

    #[test]
    fn test_identifiers() {
        assert!(smtlib_parser::identifier("willa").is_ok());
        assert!(smtlib_parser::identifier("123").is_ok());
        assert!(smtlib_parser::identifier("|zeke|").is_ok());
        assert!(smtlib_parser::identifier("(_ move over)").is_ok());
        assert!(smtlib_parser::identifier("(_ move over there)").is_ok());
        assert!(smtlib_parser::identifier("1.0").is_ok()); // parses OK, but doesn't validate

        assert!(smtlib_parser::identifier("(move over there)").is_err());
    }

    #[test]
    fn test_term() {
        // dummy term for comparison:
        // Ok(Term::QualIdentifier(QualIdentifier("x".to_string(), None)))
        assert!(smtlib_parser::term("foo").is_ok());
        assert!(smtlib_parser::term("(+ 1 (+ x 1))").is_ok());
        assert!(smtlib_parser::term("(+ (+ 1 x) x)").is_ok());
        assert!(smtlib_parser::term("(let (( y (+ 1 x))) (+ 1 y))").is_ok());
        assert_eq!(
            smtlib_parser::term("(forall ((x Int)) (> (+ 1 x) x))"),
            Ok(Term::Forall(
                vec![SortedVar(
                    Symbol("x".to_string()),
                    Sort("Int".to_string(), vec![])
                )],
                Box::new(Term::App(
                    QualIdentifier(">".to_string(), None),
                    vec![
                        Term::App(
                            QualIdentifier("+".to_string(), None),
                            vec![
                                Term::SpecConstant("1".to_string()),
                                Term::QualIdentifier(QualIdentifier("x".to_string(), None))
                            ]
                        ),
                        Term::QualIdentifier(QualIdentifier("x".to_string(), None))
                    ]
                ))
            ))
        );
        assert!(smtlib_parser::term("(exists ((x Int)) (> (+ 1 x) x))").is_ok());
        assert!(smtlib_parser::term("(exists ((x Int) (y Int)) (> (+ 1 x) y))").is_ok());
        assert!(smtlib_parser::term("(forall ((x Int)) (exists ((y Int)) (> (+ 1 x) y)))").is_ok());
        assert!(smtlib_parser::term("(match (+ 1 x) ((y (+ 1 y))))").is_ok());
        assert!(smtlib_parser::term("(cons \"abc\" (as nil (List String)))").is_ok());
        assert!(smtlib_parser::term("(select (as @a1 (Array Int Int)) 3)").is_ok());
        assert!(smtlib_parser::term("(! x :foo :bar)").is_ok());

        assert!(smtlib_parser::term(
            r#"( forall (( x ( List Int )) ( y ( List Int )))
                                         (= ( append x y )
                                            ( ite (= x ( as nil ( List Int )))
                                                  y
                                                  ( let (( h ( head x )) ( t ( tail x )))
                                                    ( insert h ( append t y ))))))"#
        )
        .is_ok());

        // TODO: this parses, but should not validate b/c "exists" is not a valid application
        // identifier
        assert!(smtlib_parser::term("(exists x Int (> (+ 1 x) x))").is_ok());

        assert!(smtlib_parser::term("(exists ((x Int) (> (+ 1 x) x))").is_err()); // missing )
        assert!(smtlib_parser::term("exists ((x Int) (> (+ 1 x) x))").is_err()); // missing (
        assert!(smtlib_parser::term("(match(+ 1 x)( (y (+ 1 y)) ))").is_err()); // not enough space
                                                                                // (const - array 0.0) is a malformed identifier
        assert!(smtlib_parser::term("(= a (as (const - array 0.0) (Array Int Real)))").is_err());
    }

    // TODO: other random expressions to parse
    //
    // ; Axiom for list append : version 1
    // ; List is a parametric datatype
    // ; with constructors " nil " and " cons "
    // ;
    // ( forall (( l1 ( List Int )) ( l2 ( List Int )))
    //   (= ( append l1 l2 )
    //      ( match l1 (
    //        ( nil l2 )
    //        (( cons h t ) ( cons h ( append t l2 )))))))
    //
    // ; Axiom for list append : version 2
    // ( forall (( l1 ( List Int )) ( l2 ( List Int )))
    //   (= ( append l1 l2 )
    //     ( match l1 (
    //       (( cons h t ) ( cons h ( append t l2 )))
    //       ( _ l2 ))))) ; _ is a variable
}
