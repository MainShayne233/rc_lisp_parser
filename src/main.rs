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

fn main() {
    let program = "(first (list 1 (+ 2 3) 9))";
    println!("Parsing: {}", program);
    let parser = expression();
    if let Ok(("", result)) = parser(program) {
        println!("Result:\n{:#?}", result);
    } else {
        println!("Parse Failure");
    }
}

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
            let next = move |next_matcher: Box<dyn Fn(&str) -> Result<(&str, Node), &str>>| {
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

#[test]
fn test_and_then() {
    let parser = and_then(left_paren(), and_then(identifier(), whitespace()));
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
        parser("(hello ")
    );
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

fn left_paren() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_single_char(|c| c == '(', |_| Node::LeftParen)
}

fn right_paren() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_single_char(|c| c == ')', |_| Node::RightParen)
}

#[test]
fn test_parse_parens() {
    assert_eq!(Ok(("", Node::LeftParen)), left_paren()("("));
    assert_eq!(Ok(("", Node::RightParen)), right_paren()(")"));
}

fn whitespace() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_some_chars(char::is_whitespace, new_whitespace)
}

#[test]
fn test_whitespace() {
    let parser = whitespace();
    assert_eq!(Ok(("", Node::Whitespace)), parser(" "));
}

fn integer() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_some_chars(char::is_numeric, new_integer)
}

#[test]
fn test_integer() {
    let parser = integer();
    assert_eq!(Ok(("", Node::Integer(1))), parser("1"));
    assert_eq!(Ok(("", Node::Integer(2))), parser("2"));
    assert_eq!(Ok(("", Node::Integer(123))), parser("123"));
    assert_eq!(Err("apple"), parser("apple"));
}

fn identifier() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_some_chars(char::is_alphabetic, new_identifier)
}

#[test]
fn test_identifier() {
    let parser = identifier();
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("apple")))),
        parser("apple")
    );
    assert_eq!(Err("+cool"), parser("+cool"));
    assert_eq!(Err("123"), parser("123"));
}

fn operator() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    match_single_char(is_operator, new_operator)
}

#[test]
fn test_operator() {
    let parser = operator();
    assert_eq!(Ok(("", Node::FunctionName(String::from("+")))), parser("+"));
    assert_eq!(Ok(("", Node::FunctionName(String::from("-")))), parser("-"));
    assert_eq!(
        Ok(("cool", Node::FunctionName(String::from("+")))),
        parser("+cool")
    );
}

fn function_name() -> impl Fn(&str) -> Result<(&str, Node), &str> {
    or(identifier(), operator())
}

#[test]
fn test_function_name() {
    let parser = function_name();
    assert_eq!(
        Ok(("", Node::FunctionName(String::from("hello")))),
        parser("hello")
    );
    assert_eq!(Ok(("", Node::FunctionName(String::from("+")))), parser("+"));
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
    move |input| match left_paren()(input) {
        Ok(_) => function_call()(input),
        _ => integer()(input),
    }
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
