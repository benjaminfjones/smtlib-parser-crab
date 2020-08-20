use smtlib_parser_crab::parser::smtlib_parser;

pub fn main() {
    let my_num = smtlib_parser::numeral("1").unwrap();
    println!("my_num: {:?}", my_num);
    assert_eq!(my_num, "1");
}
