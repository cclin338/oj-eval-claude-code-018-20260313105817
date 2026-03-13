/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 *
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <numeric>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Helper function to compute GCD (declared in expr.cpp)
extern int gcd(int a, int b);

// Helper function to simplify rational numbers
std::pair<int, int> simplify_rational(int num, int den) {
    if (den == 0) throw RuntimeError("Division by zero");
    if (den < 0) {
        num = -num;
        den = -den;
    }
    int g = gcd(num < 0 ? -num : num, den < 0 ? -den : den);
    if (g == 0) g = 1;
    return {num / g, den / g};
}

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto& rand : rands) {
        args.push_back(rand->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                {E_VOID,     {new MakeVoid(), {}}},
                {E_EXIT,     {new Exit(), {}}},
                {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                {E_LISTQ,    {new IsList(new Var("parm")), {"parm"}}},
                {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                {E_CAR,      {new Car(new Var("parm")), {"parm"}}},
                {E_CDR,      {new Cdr(new Var("parm")), {"parm"}}},
                {E_NOT,      {new Not(new Var("parm")), {"parm"}}},
                {E_PLUS,     {new PlusVar({}),  {}}},
                {E_MINUS,    {new MinusVar({}), {}}},
                {E_MUL,      {new MultVar({}),  {}}},
                {E_DIV,      {new DivVar({}),   {}}},
                {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_CONS,     {new Cons(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_SETCAR,   {new SetCar(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_SETCDR,   {new SetCdr(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EQQ,      {new IsEq(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_LT,       {new LessVar({}), {}}},
                {E_LE,       {new LessEqVar({}), {}}},
                {E_EQ,       {new EqualVar({}), {}}},
                {E_GE,       {new GreaterEqVar({}), {}}},
                {E_GT,       {new GreaterVar({}), {}}},
                {E_LIST,     {new ListFunc({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                return ProcedureV(it->second.second, it->second.first, e);
            }
        }
        throw RuntimeError("Undefined variable: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n + dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        auto result = simplify_rational(r1->numerator + n2 * r1->denominator, r1->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(n1 * r2->denominator + r2->numerator, r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(r1->numerator * r2->denominator + r2->numerator * r1->denominator,
                                       r1->denominator * r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    }
    throw RuntimeError("Wrong typename in +");
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n - dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        auto result = simplify_rational(r1->numerator - n2 * r1->denominator, r1->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(n1 * r2->denominator - r2->numerator, r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(r1->numerator * r2->denominator - r2->numerator * r1->denominator,
                                       r1->denominator * r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    }
    throw RuntimeError("Wrong typename in -");
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n * dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        auto result = simplify_rational(r1->numerator * n2, r1->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(n1 * r2->numerator, r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        auto result = simplify_rational(r1->numerator * r2->numerator, r1->denominator * r2->denominator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    }
    throw RuntimeError("Wrong typename in *");
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        auto result = simplify_rational(n1, n2);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        auto result = simplify_rational(r1->numerator, r1->denominator * n2);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        auto result = simplify_rational(n1 * r2->denominator, r2->numerator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    } else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        auto result = simplify_rational(r1->numerator * r2->denominator, r1->denominator * r2->numerator);
        if (result.second == 1) return IntegerV(result.first);
        return RationalV(result.first, result.second);
    }
    throw RuntimeError("Wrong typename in /");
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) return IntegerV(0);
    if (args.size() == 1) return args[0];
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = Plus(new Fixnum(0), new Fixnum(0)).evalRator(result, args[i]);
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw RuntimeError("- requires at least one argument");
    if (args.size() == 1) {
        if (args[0]->v_type == V_INT) {
            return IntegerV(-dynamic_cast<Integer*>(args[0].get())->n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw RuntimeError("Wrong typename in -");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = Minus(new Fixnum(0), new Fixnum(0)).evalRator(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) return IntegerV(1);
    if (args.size() == 1) return args[0];
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = Mult(new Fixnum(0), new Fixnum(0)).evalRator(result, args[i]);
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw RuntimeError("/ requires at least one argument");
    if (args.size() == 1) {
        // (/ x) returns 1/x
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            if (n == 0) throw RuntimeError("Division by zero");
            auto result = simplify_rational(1, n);
            if (result.second == 1) return IntegerV(result.first);
            return RationalV(result.first, result.second);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            if (r->numerator == 0) throw RuntimeError("Division by zero");
            auto result = simplify_rational(r->denominator, r->numerator);
            if (result.second == 1) return IntegerV(result.first);
            return RationalV(result.first, result.second);
        }
        throw RuntimeError("Wrong typename in /");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = Div(new Fixnum(0), new Fixnum(0)).evalRator(result, args[i]);
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        long long result = 1;
        long long b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        long long left = (long long)r1->numerator * r2->denominator;
        long long right = (long long)r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) throw RuntimeError("< requires at least 2 arguments");
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i + 1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) throw RuntimeError("<= requires at least 2 arguments");
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i + 1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) throw RuntimeError("= requires at least 2 arguments");
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i + 1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) throw RuntimeError(">= requires at least 2 arguments");
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i + 1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) throw RuntimeError("> requires at least 2 arguments");
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i + 1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    if (args.empty()) return NullV();
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = PairV(args[i], result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    Value current = rand;
    while (current->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(current.get());
        current = p->cdr;
    }
    return BooleanV(current->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car expects a pair");
    }
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr expects a pair");
    }
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car! expects a pair");
    }
    dynamic_cast<Pair*>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr! expects a pair");
    }
    dynamic_cast<Pair*>(rand1.get())->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) return VoidV();
    Value result = VoidV();
    for (auto& expr : es) {
        result = expr->eval(e);
    }
    return result;
}

// Helper function to convert Syntax to Value
Value syntaxToValue(const Syntax &s);

Value Quote::eval(Assoc& e) {
    return syntaxToValue(s);
}

// Convert syntax to value for quote
Value syntaxToValue(const Syntax &s) {
    if (auto num = dynamic_cast<Number*>(s.get())) {
        return IntegerV(num->n);
    } else if (auto rat = dynamic_cast<RationalSyntax*>(s.get())) {
        return RationalV(rat->numerator, rat->denominator);
    } else if (auto str = dynamic_cast<StringSyntax*>(s.get())) {
        return StringV(str->s);
    } else if (dynamic_cast<TrueSyntax*>(s.get())) {
        return BooleanV(true);
    } else if (dynamic_cast<FalseSyntax*>(s.get())) {
        return BooleanV(false);
    } else if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) {
        return SymbolV(sym->s);
    } else if (auto list = dynamic_cast<List*>(s.get())) {
        if (list->stxs.empty()) {
            return NullV();
        }
        Value result = NullV();
        for (int i = list->stxs.size() - 1; i >= 0; i--) {
            result = PairV(syntaxToValue(list->stxs[i]), result);
        }
        return result;
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    Value result = BooleanV(true);
    for (auto& rand : rands) {
        result = rand->eval(e);
        // Short-circuit: if false, return immediately
        if (result->v_type == V_BOOL && !dynamic_cast<Boolean*>(result.get())->b) {
            return BooleanV(false);
        }
    }
    return result;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (auto& rand : rands) {
        Value result = rand->eval(e);
        // Short-circuit: if not false, return the value
        if (result->v_type != V_BOOL || dynamic_cast<Boolean*>(result.get())->b) {
            return result;
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) {
        return BooleanV(true);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value cond_val = cond->eval(e);
    bool is_true = !(cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b);
    if (is_true) {
        return conseq->eval(e);
    } else {
        return alter->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (auto& clause : clauses) {
        if (clause.empty()) continue;

        // Check if it's an else clause
        if (auto var = dynamic_cast<Var*>(clause[0].get())) {
            if (var->x == "else") {
                if (clause.size() == 1) return VoidV();
                Value result = VoidV();
                for (size_t i = 1; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }

        // Evaluate condition
        Value cond_val = clause[0]->eval(env);
        bool is_true = !(cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b);

        if (is_true) {
            if (clause.size() == 1) return cond_val;
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value rator_val = rator->eval(e);
    if (rator_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure* clos_ptr = dynamic_cast<Procedure*>(rator_val.get());

    // Evaluate arguments
    std::vector<Value> args;
    for (auto& r : rand) {
        args.push_back(r->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    // Create new environment with parameters bound to arguments
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Check if variable already exists
    Value existing = find(var, env);

    // Check if it's a lambda definition for recursion support
    if (auto lambda = dynamic_cast<Lambda*>(e.get())) {
        if (existing.get() != nullptr) {
            // Variable exists, modify it with placeholder first
            modify(var, Value(nullptr), env);
            Value proc_val = e->eval(env);
            modify(var, proc_val, env);
        } else {
            // Variable doesn't exist, extend with placeholder first
            env = extend(var, Value(nullptr), env);
            Value proc_val = e->eval(env);
            modify(var, proc_val, env);
        }
        return VoidV();
    }

    Value val = e->eval(env);
    if (existing.get() != nullptr) {
        // Variable exists, modify it
        modify(var, val, env);
    } else {
        // Variable doesn't exist, extend the environment
        env = extend(var, val, env);
    }
    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Evaluate all binding expressions in current environment
    std::vector<Value> values;
    for (auto& b : bind) {
        values.push_back(b.second->eval(env));
    }

    // Create new environment with bindings
    Assoc new_env = env;
    for (size_t i = 0; i < bind.size(); i++) {
        new_env = extend(bind[i].first, values[i], new_env);
    }

    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Create environment with placeholder bindings
    Assoc env1 = env;
    for (auto& b : bind) {
        env1 = extend(b.first, Value(nullptr), env1);
    }

    // Evaluate binding expressions and update environment
    for (auto& b : bind) {
        Value val = b.second->eval(env1);
        modify(b.first, val, env1);
    }

    return body->eval(env1);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
