extern crate peg;

#[allow(dead_code)]
const RESERVED_WORDS: [&'static str; 13] = [
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

peg::parser!{
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
        rule quoted_symbol() -> &'input str
            = $("|" quoted_symbol_char()* "|")
        pub rule symbol() -> &'input str
            = $(simple_symbol() / quoted_symbol())
        pub rule keyword() -> &'input str
            = $(":" simple_symbol())

        // S-expressions
        rule spec_constant() -> &'input str
            = $(numeral() / decimal() / hexadecimal() / binary() / string())
        pub rule s_expr() -> &'input str
            = $(spec_constant() / symbol() / keyword() / "(" _ (s_expr() ** __) _ ")")

        // identifiers
        rule index() -> &'input str
            = $(numeral() / symbol())
        pub rule identifier() -> &'input str
            = $(symbol() / "(" _ "_" _ (index() **<1,> __) _ ")")

        // attributes
        // TODO: parse attribute values
        rule attribute_value() -> &'input str
            = $(spec_constant() / symbol() / "(" _ (s_expr() ** __) _ ")")
        pub rule attribute() -> Attribute
            = k:keyword() v:attribute_value()? { Attribute(Keyword(k.to_string()), v.map(|s| s.to_string())) }

        // sorts
        pub rule sort() -> &'input str
            = $(identifier() / "(" _ identifier() _ (sort() **<1,> __) _ ")")

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
        rule qual_identifier() -> &'input str
            = $(identifier() / "(" _ "as" __ identifier() __ sort() _ ")")
        rule var_binding() -> &'input str
            = $("(" _ symbol() __ term() _ ")")
        rule sorted_var() -> &'input str
            = $("(" _ symbol() __ sort() _ ")")
        rule pattern() -> &'input str
            = $(symbol() / "(" _ symbol() __ (symbol() **<1,> __) _ ")")
        rule match_case() -> &'input str
            = $("(" _ pattern() __ term() _ ")")
        pub rule term() -> Term
            = s:spec_constant() { Term::spec_constant(s) }
            / i:qual_identifier() { Term::qual_identifier(i) }
            / "(" _ i:qual_identifier() __ ts:(term() **<1,> __) _ ")" { Term::app(i, ts) }
            // / "(" _ "let" __ "(" vbs:(var_binding() **<1,> __) t:term() _ ")" { Term::let(vbs, t) }
            // / "(" _ "forall" __ "(" svs:(sorted_var() **<1,> __) t:term() _ ")" { Term::forall(svs, t) }
            // / "(" _ "exists" __ "(" svs:(sorted_var() **<1,> __) t:term() _ ")" { Term::exists(svs, t) }
            // / "(" _ "match" __ t:term() "(" mcs:(match_case() **<1,> __) _ ")" { Term::mtch(t, mcs) }
            // / "(" _ "!" __ t:term() as:(attribute() **<1,> __) _ ")" { Term::bang(t, as) }
    }
}

// newtypes for use in Term
pub struct Symbol(String);
pub struct Sort(String);
pub struct VarBinding(Symbol, Box<Term>);
pub struct SortedVar(Symbol, Sort);
pub struct Pattern(Symbol, Vec<Symbol>);
pub struct MatchCase(Pattern, Box<Term>);
pub struct Keyword(String);
pub struct Attribute(Keyword, Option<String>);

pub enum Term {
    SpecConstant(String),
    QualIdentifier(String),
    App(String, Vec<Box<Term>>),
    Let(Vec<VarBinding>, Box<Term>),
    Forall(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    Match(Box<Term>, Vec<MatchCase>),
    Bang(Box<Term>, Vec<Attribute>),
}

impl Term {
    pub fn spec_constant(s: &str) -> Self {
        Term::SpecConstant(s.to_string())
    }

    pub fn qual_identifier(s: &str) -> Self {
        Term::QualIdentifier(s.to_string())
    }

    pub fn app(i: &str, ts: Vec<Term>) -> Self {
        Term::App(i.to_string(), ts.into_iter().map(|t| Box::new(t)).collect())
    }

    // TODO: finish the rest of the smart constructors
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
        assert_eq!(smtlib_parser::string("\"hello world\""), Ok("\"hello world\""));
        assert_eq!(smtlib_parser::string("\"she said \"\"hello world\"\"\""), Ok("\"she said \"\"hello world\"\"\""));
        let multi_line = r#""this is a string literal
        with a line break in it""#;
        assert_eq!(smtlib_parser::string(multi_line), Ok(multi_line));
        assert!(smtlib_parser::string("\"bad \"news\"").is_err())
    }

    #[test]
    fn test_symbol() {
        assert_eq!(smtlib_parser::symbol("|symbol|"), Ok("|symbol|"));
        assert!(smtlib_parser::symbol("FOOBAR").is_ok());
        assert!(smtlib_parser::symbol("!foo").is_ok());
        assert!(smtlib_parser::symbol("~~~").is_ok());
        assert!(smtlib_parser::symbol("foo01").is_ok());
        assert!(smtlib_parser::symbol("BINARY").is_ok());  // parses OK, but shouldn't validate
        assert!(smtlib_parser::symbol("1.0").is_ok());     // parses OK, but doesn't validate
        assert!(smtlib_parser::symbol("0foo").is_ok());    // parses OK, but doesn't validate
        assert!(smtlib_parser::symbol("|foo\"bar|").is_ok());
        assert!(smtlib_parser::symbol("||").is_ok());
        assert!(smtlib_parser::symbol(r#"|af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ’]]984|"#).is_ok());

        let multi_line = r#"|this is a symbol
        with a line break in it|"#;
        assert!(smtlib_parser::symbol(multi_line).is_ok());

        // negative parses
        assert!(smtlib_parser::symbol("|sym|ol|").is_err());
        assert!(smtlib_parser::symbol(r#"|sym\ol|"#).is_err());
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
        assert!(smtlib_parser::identifier("1.0").is_ok());  // parses OK, but doesn't validate

        assert!(smtlib_parser::identifier("(move over there)").is_err());
    }

    // TODO: test term()
}
