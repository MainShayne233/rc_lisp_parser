#![feature(box_syntax, box_patterns)]
//////////////////////////////////////////////////////////////////////////////////////////////////
// Lisp parser                                                                                  //
//                                                                                              //
// Write code that takes some Lisp code and returns an abstract syntax tree. The AST should     //
// represent the structure of the code and the meaning of each token. For example, if your code //
// is given "(first (list 1 (+ 2 3) 9))", it could return a nested array                        //
// like ["first", ["list", 1, ["+", 2, 3], 9]].                                                 //
//////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
enum Node {
    LeftParen,
    RightParen,
    Whitespace,
    Nothing,
    Integer(i64),
    FunctionName(String),
    FunctionCall(Box<(Node, Vec<Node>)>),
    Pair(Box<(Node, Node)>),
    List(Box<Vec<Node>>),
}

// fn main() {
//     let parse_expression = or(vec![parse_integer, parse_function]);
//     let parse_function = match_pattern(vec![
//         literal(left_paren),
//         any_amount(whitespace()),
//         or(vec![identifier, operator]),
//         any_amount(whitespace()),
//         many(
//             whitespace_delimited(expression)
//         )
//        any_amount(whitespace()),
//        literal(right_paren),
//     ]);
// }

fn or<L, R>(lhs_matcher: L, rhs_matcher: R) -> impl Fn(&str) -> Result<(&str, Node), &str>
where
    L: Fn(&str) -> Result<(&str, Node), &str>,
    R: Fn(&str) -> Result<(&str, Node), &str>,
{
    move |input| match lhs_matcher(input) {
        Ok((rest, node)) => Ok((rest, node)),
        _ => match rhs_matcher(input) {
            Ok((rest, node)) => Ok((rest, node)),
            _ => Err(input),
        },
    }
}

fn and_then<L, R>(lhs_matcher: L, rhs_matcher: R) -> impl Fn(&str) -> Result<(&str, Node), &str>
where
    L: Fn(&str) -> Result<(&str, Node), &str>,
    R: Fn(&str) -> Result<(&str, Node), &str>,
{
    move |input| match lhs_matcher(input) {
        Ok((rest, lhs_result)) => {
            let next = move |next_matcher: Box<Fn(&str) -> Result<(&str, Node), &str>>| {
                match next_matcher(rest) {
                    Ok((rest, rhs_result)) => {
                        Ok((rest, Node::Pair(Box::new((lhs_result, rhs_result)))))
                    }
                    _ => Err(input),
                }
            };
            next(Box::new(|rest| rhs_matcher(rest)))
        }
        _ => match rhs_matcher(input) {
            Ok((rest, node)) => Ok((rest, node)),
            _ => Err(input),
        },
    }
}


fn whitespace_delimited<L>(matcher: L) -> impl Fn(&str) -> Result<(&str, Node), &str>
where
    L: Fn(&str) -> Result<(&str, Node), &str>,
{
    move |input| {
        let mut matches: Vec<Node> = vec![];
        let mut current = input;
        while let Ok((rest, result)) = or(|input| matcher(input), whitespace())(current) {
            if result != Node::Whitespace {
                matches.push(result);
            }
            current = rest;
        }
        Ok((current, Node::List(Box::new(matches))))
    }
}

fn match_some_chars<T, P, R>(predicate: P, reducer: R) -> impl Fn(&str) -> Result<(&str, T), &str>
where
    P: Fn(char) -> bool,
    R: Fn(String) -> T,
{
    move |input| {
        let mut matched = String::new();
        let mut chars = input.chars();

        match chars.next() {
            Some(next) if predicate(next) => matched.push(next),
            _ => return Err(input),
        }

        while let Some(next) = chars.next() {
            if predicate(next) {
                matched.push(next);
            } else {
                break;
            }
        }

        let next_index = matched.len();
        Ok((&input[next_index..], reducer(matched)))
    }
}

fn match_single_char<T, P, R>(predicate: P, reducer: R) -> impl Fn(&str) -> Result<(&str, T), &str>
where
    P: Fn(char) -> bool,
    R: Fn(char) -> T,
{
    move |input| match input.chars().next() {
        Some(next) if predicate(next) => Ok((&input[1..], reducer(next))),
        _ => return Err(input),
    }
}

fn new_integer(value: String) -> Node {
    Node::Integer(value.parse::<i64>().unwrap())
}

fn new_identifier(value: String) -> Node {
    Node::FunctionName(value)
}

fn new_operator(value: char) -> Node {
    let mut string = String::new();
    string.push(value);
    Node::FunctionName(string)
}

fn new_whitespace(_: String) -> Node {
    Node::Whitespace
}

fn is_operator(value: char) -> bool {
    value == '+' || value == '-' || value == '*' || value == '/'
}

fn is_symbol(value: char) -> bool {
    value == ')' || value == '('
}

#[test]
fn test_parse_integer() {
    let parse_integer = match_some_chars(char::is_numeric, new_integer);
    assert_eq!(Ok(("", Node::Integer(1))), parse_integer("1"));
    assert_eq!(Ok(("", Node::Integer(2))), parse_integer("2"));
    assert_eq!(Ok(("", Node::Integer(123))), parse_integer("123"));
    assert_eq!(Err("apple"), parse_integer("apple"));
}

#[test]
fn test_parse_identifier() {
    let parse_identifier = match_some_chars(char::is_alphabetic, new_identifier);
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("apple")))),
        parse_identifier("apple")
    );
    assert_eq!(Err("+cool"), parse_identifier("+cool"));
    assert_eq!(Err("123"), parse_identifier("123"));
}

#[test]
fn test_parse_operator() {
    let parse_operator = match_single_char(is_operator, new_operator);
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("+")))),
        parse_operator("+")
    );
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("-")))),
        parse_operator("-")
    );
    assert_eq!(
        Ok(("cool", Node::FunctionName(String::from("+")))),
        parse_operator("+cool")
    );
}

#[test]
fn test_parse_function_name() {
    let parse_identifier = match_some_chars(char::is_alphabetic, new_identifier);
    let parse_operator = match_single_char(is_operator, new_operator);
    let parse_either = or(parse_identifier, parse_operator);
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("hello")))),
        parse_either("hello")
    );
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("+")))),
        parse_either("+")
    );
}

#[test]
fn test_left_paren_then_identifier_then_whitespace() {
    let parse_left_paren = match_single_char(|c| c == '(', |_| Node::LeftParen);
    let parse_ident = match_some_chars(char::is_alphabetic, new_identifier);
    let parse_whitespace = match_some_chars(char::is_whitespace, new_whitespace);
    let parse_all = and_then(parse_left_paren, and_then(parse_ident, parse_whitespace));
    assert_eq!(
        Ok((
            "",
            Node::Pair(Box::new((
                Node::LeftParen,
                Node::Pair(Box::new((
                    Node::FunctionName(String::from("hello")),
                    Node::Whitespace,
                ))),
            )))
        )),
        parse_all("(hello ")
    );
}

#[test]
fn test_parse_whitespace() {
    let parse_whitespace = match_some_chars(char::is_whitespace, new_whitespace);
    assert_eq!(Ok(("", Node::Whitespace)), parse_whitespace(" "));
}

#[test]
fn test_parse_parens() {
    let parse_left_paren = match_single_char(|c| c == '(', |_| Node::LeftParen);
    let parse_right_paren = match_single_char(|c| c == ')', |_| Node::RightParen);
    assert_eq!(Ok(("", Node::LeftParen)), parse_left_paren("("));
    assert_eq!(Ok(("", Node::RightParen)), parse_right_paren(")"));
}

fn left_paren() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_single_char(|c| c == '(', |_| Node::LeftParen)
}

fn right_paren() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_single_char(|c| c == ')', |_| Node::RightParen)
}

fn whitespace() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_some_chars(char::is_whitespace, new_whitespace)
}

fn integer() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_some_chars(char::is_numeric, new_integer)
}

fn function_name() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    let parse_identifier = match_some_chars(char::is_alphabetic, new_identifier);
    let parse_operator = match_single_char(is_operator, new_operator);
    or(parse_identifier, parse_operator)
}

fn maybe<L>(matcher: L) -> impl Fn(&str) -> Result<(&str, Node), &str>
where
    L: Fn(&str) -> Result<(&str, Node), &str>,
{
    move |input| match matcher(input) {
        Ok((rest, result)) => Ok((rest, result)),
        Err(_) => Ok((input, Node::Nothing)),
    }
}

fn expression() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    integer()
}

fn function_arguments() -> impl Fn(&str) -> Result<(&str, Node), &str> {
     move |input| match whitespace_delimited(expression())(input) {
        Ok((rest, Node::List(box mut args))) => match expression()(rest) {
            Ok((rest, trailing_arg)) => {
                args.push(trailing_arg);
                Ok((rest, Node::List(Box::new(args))))
            }
            _ => Ok((rest, Node::List(Box::new(args)))),
        },
        _ => Err(input),
    }
}

fn function_call() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    let parser = and_then(
        left_paren(),
        and_then(
            maybe(whitespace()),
            and_then(
                function_name(),
                or(
                    right_paren(),
                    and_then(
                        whitespace(),
                        and_then(
                            function_arguments(),
                            and_then(maybe(whitespace()), right_paren()),
                        ),
                    ),
                ),
            ),
        ),
    );
    move |input| match parser(input) {
        Ok((
            rest,
            Node::Pair(box (
                Node::LeftParen,
                Node::Pair(box (_, Node::Pair(box (function_name, Node::RightParen)))),
            )),
        )) => Ok((rest, Node::FunctionCall(Box::new((function_name, vec![]))))),
        Ok((
            rest,
            Node::Pair(box (
                Node::LeftParen,
                Node::Pair(box (
                    _,
                    Node::Pair(box (
                        function_name,
                        Node::Pair(box (
                            _,
                            Node::Pair(box (
                                Node::List(box args),
                                Node::Pair(box (_, Node::RightParen)),
                            )),
                        )),
                    )),
                )),
            )),
        )) => Ok((rest, Node::FunctionCall(Box::new((function_name, args))))),
        Err(_) => Err(input),
        other => other,
    }
}

#[test]
fn test_zero_arity_function_call() {
    let parser = function_call();
    assert_eq!(
        Ok((
            "",
            Node::FunctionCall(Box::new((Node::FunctionName("hello".to_string()), vec![])))
        )),
        parser("(hello)")
    )
}

#[test]
fn test_single_arg_function_call() {
    let parser = function_call();
    assert_eq!(
        Ok((
            "",
            Node::FunctionCall(Box::new((
                Node::FunctionName("print".to_string()),
                vec![Node::Integer(1)]
            )))
        )),
        parser("(print 1)")
    )
}

#[test]
fn test_three_arg_function_call() {
    let parser = function_call();
    assert_eq!(
        Ok((
            "",
            Node::FunctionCall(Box::new((
                Node::FunctionName("add".to_string()),
                vec![Node::Integer(1), Node::Integer(2), Node::Integer(3)]
            )))
        )),
        parser("(add 1 2 3)")
    )
}

#[test]
fn test_nested_function_call() {
    let parser = function_call();
    assert_eq!(
        Ok((
            "",
            Node::FunctionCall(Box::new((
                Node::FunctionName("add".to_string()),
                vec![
                    Node::FunctionCall(Box::new((
                        Node::FunctionName("add".to_string()),
                        vec![Node::Integer(1), Node::Integer(2)]
                    ))),
                    Node::Integer(3)
                ]
            )))
        )),
        parser("(add (add 1 2) 3)")
    )
}
