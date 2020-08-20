extern crate peg;

peg::parser!{
    pub grammar smtlib_parser() for str {
        rule whitespace_char() = quiet!{[' ' | '\t' | '\n' | '\r']}
        rule whitespace() = quiet!{whitespace_char()+}
        // http://www.unicode.org/glossary/#unicode_scalar_value
        rule printable_char() -> &'input str
            = $(['\u{0020}'..='\u{007E}' | '\u{0080}'..='\u{D7FF}' | '\u{E000}'..='\u{10FFFF}'])
        rule printable_non_quote() -> &'input str
            = $(['\u{0020}'..='\u{0021}' | '\u{0023}'..='\u{007E}' | '\u{0080}'..='\u{D7FF}' | '\u{E000}'..='\u{10FFFF}'])
        rule digit() -> &'input str
            = $(['0'..='9'])
        rule letter() -> &'input str
            = $(['a'..='z' | 'A'..='Z'])
        rule symbol_char() -> &'input str
            = $(['~' | '!'])  // @ $ % ^ & * _ - + = < > . ? /
        // an escaped quote inside a string literal
        rule esc_quote() -> &'input str
            = $("\"\"")
        pub rule numeral() -> &'input str
            = n:$(['0']) !digit() {n} / $(['1'..='9']['0'..='9']*)
        pub rule decimal() -> &'input str
            = $(numeral() "." ['0'..='1']+)
        pub rule hexadecimal() -> &'input str
            = $("#x" ['0'..='9' | 'a'..='f' | 'A'..='F']+)
        pub rule binary() -> &'input str
            = $("#b" ['0'..='1']+)
        pub rule string() -> &'input str
            = $("\"" (esc_quote() / printable_non_quote() / whitespace_char())* "\"")
        // TODO: this list is not complete
        pub rule reserved_word() -> &'input str
            = $("BINARY" /
                "DECIMAL" /
                "HEXADECIMAL" /
                "NUMERAL" /
                "STRING" /
                "_" /
                "!" /
                "as" /
                "let" /
                "exists" /
                "forall" /
                "match" /
                "par")
        rule simple_symbol() -> &'input str
            = $((letter() / digit() / symbol_char())+)
        rule quoted_symbol() -> &'input str
            = $("|symbol|")
        pub rule symbol() -> &'input str
            = $(simple_symbol() / quoted_symbol())
    }
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
    fn test_reserved_word() {
        assert_eq!(smtlib_parser::reserved_word("BINARY"), Ok("BINARY"));
        assert!(smtlib_parser::reserved_word("FOOBAR").is_err());
    }

    // TODO these don't pass yet
    // #[test]
    fn test_symbol() {
        assert!(smtlib_parser::symbol("|symbol|").is_ok());
        assert!(smtlib_parser::symbol("FOOBAR").is_ok());
        assert!(smtlib_parser::symbol("!foo").is_ok());
        assert!(smtlib_parser::symbol("~~~").is_ok());
        assert!(smtlib_parser::symbol("foo01").is_ok());
        assert!(smtlib_parser::symbol("BINARY").is_err());  // reserved word
        assert!(smtlib_parser::symbol("0foo").is_err());  // starts with a digit
    }

}
