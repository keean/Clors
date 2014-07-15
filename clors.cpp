// Copyright 2012, 2013, 2014 Keean Schupke
// compile with g++ -std=gnu++11 

#include <string>
#include <vector>
#include <forward_list>
#include <iostream>
#include <iomanip>
#include <memory>
#include <fstream>
#include <stdexcept>
#include <vector>
#include <deque>
#include <map>
#include <unordered_map>
#include <set>
#include <sstream>
#include <type_traits>

#include <ctime>

extern "C" {
#include <sys/resource.h>
}

using namespace std;

//----------------------------------------------------------------------------
// Profiling

inline uint64_t rtime() {
    struct rusage rusage;
    getrusage(RUSAGE_SELF, &rusage);
    return 1000000 * static_cast<uint64_t>(rusage.ru_utime.tv_sec) + static_cast<uint64_t>(rusage.ru_utime.tv_usec);
}

class profile {
    static uint64_t t;
    static uint64_t s;

public:
    profile() {
        s = rtime();
    }

    ~profile() {
        t += rtime() - s;
    }

    static void start() {
        s = rtime();
    }

    static void finish() {
        t += rtime() - s;
    }

    static uint64_t report() {
        return t;
    }
};

uint64_t profile::t {0};
uint64_t profile::s;

class depth_profile {
    int const depth;

public:
    depth_profile(int const i) : depth(i) {
        profile::start();
    }
    ~depth_profile() {
        profile::finish();
        cout << "DEPTH " << depth << " ELAPSED TIME: " << profile::report() << "us\n";
    }
};

//----------------------------------------------------------------------------
// Character Predicates

struct is_space {
    string const name = "space";
    bool operator() (int const c) const {
        return ::isspace(c) != 0;
    }
} is_space;

struct is_digit {
    string const name = "digit";
    bool operator() (int const c) const {
        return ::isdigit(c) != 0;
    }
} is_digit;

struct is_upper {
    string const name = "uppercase";
    bool operator() (int const c) const {
        return ::isupper(c) != 0;
    }
} is_upper;

struct is_lower {
    string const name = "lowercase";
    bool operator() (int const c) const {
        return ::islower(c) != 0;
    }
} is_lower;

struct is_alpha {
    string const name = "alphabetic";
    bool operator() (int const c) const {
        return ::isalpha(c) != 0;
    }
} is_alpha;

struct is_alnum {
    string const name = "alphanumeric";
    bool operator() (int const c) const {
        return ::isalnum(c) != 0;
    }
} is_alnum;

class is_char {
    int const k;

public:
    string const name;
    explicit is_char(char const c) : k(c), name("'" + string(1, c) + "'")  {}
    bool operator() (int const c) const {
        return k == c;
    }
};

template <typename T, typename U> class is_either {
    T const& a;
    U const& b;

public:
    string const name;
    is_either(T const& a, U const& b) : a(a), b(b), name("(" + a.name + " or " + b.name + ")") {}
    bool operator() (int const c) const {
        return a(c) || b(c);
    }
};

template <typename T> class is_not {
    T const& a;

public:
    string const name;
    is_not(T const& a) : a(a), name("~" + a.name) {}
    bool operator() (int const c) const {
        return !a(c);
    }
};

//----------------------------------------------------------------------------
// Recursive Descent Parser

struct parse_error : public runtime_error {
    int const row;
    int const col;
    int const sym;
    string const exp;
    parse_error(string const& what, int row, int col, string exp, int sym)
        : runtime_error(what), row(row), col(col), exp(move(exp)), sym(sym) {}
};

class fparse {
    fstream *in;
    int row;
    int col;
    int sym;

protected:
    void next() {
        sym = in->get();
        if (sym == '\n') {
            ++row;
            col = 1;
        } else {
            ++col;
        }
    }
    
    void error(string const& err, string const exp) {
        throw parse_error(err, row, col, exp, sym);
    }

    template <typename Term> bool test(Term const& t) {
        return t(sym);
    }

    template <typename Term> bool accept(Term const& t, string *s = nullptr) {
        if (t(sym)) {
            if (s != nullptr) {
                s->push_back(sym);
            }
            next();
            return true;
        }
        return false;
    }

    template <typename Term> void expect(Term const& t, string *s = nullptr) {
        if (!t(sym)) {
            error("expected", t.name);   
        }
        if (s != nullptr) {
            s->push_back(sym);
        }
        next();
    }

    void space(string *s = nullptr) {
        while (accept(is_space, s));
    }

    void number(string *s = nullptr) {
        expect(is_digit, s);
        while (accept(is_digit, s));
    }

    void name(string *s = nullptr) {
        expect(is_alpha, s);
        while (accept(is_alnum, s));
    }

    void set_fstream(fstream *f) {
        in = f;
        row = 1;
        col = 1;
        sym = f->get();
    }
};

//----------------------------------------------------------------------------
// Clause Environment

class type_expression;
class type_variable;
class type_atom;
class type_struct;
class type_clause;
class type_source;

enum class kleene3 {
    k3_true,
    k3_false,
    k3_unknown
};

using env_type = map<type_atom*, vector<type_clause*>>;
using atoms = map<string, type_atom*>;

//----------------------------------------------------------------------------
// Fluent

struct fluent {
    virtual ~fluent() {}
};

struct source : public fluent {
    virtual type_clause* get() = 0;
    virtual type_clause* reget() = 0;
    virtual void stop() {} 
    virtual bool at_end() {
        return true;
    }
};

struct sink : public fluent {
    virtual void put(type_expression*) = 0;
};

//----------------------------------------------------------------------------
// Expression Graph

struct ast {
    virtual ~ast() {};
};

typedef vector<pair<type_expression *const, bool const>> union_stack;

class type_expression : public ast {
    type_expression *canonical;
    int rank;

protected:
    type_expression() : canonical(this), rank(0) {}

public:
    virtual void accept(class type_visitor *v) = 0;

    void deunion(bool ranked) {
        if (ranked) {
            --(canonical->rank);
        }
        canonical = this;

    }

    // find the canonical type
    friend type_expression* find(type_expression* e) {
        while (e != e->canonical) {
            e = e->canonical;
        }
        return e;
    }
   
    // let the algorithm pick the most efficient substitution
    friend void link(type_expression* x, type_expression* y, union_stack& u) {
        bool ranked = false;
        if (x->rank > y->rank) {
            swap(x, y);
        } else if (x->rank == y->rank) {
            ranked = true;
            ++(y->rank);
        }
        x->canonical = y;
        u.emplace_back(x, ranked);
    }

    void replace_with(type_expression *e, union_stack& u) {
        bool const ranked = (rank == e->rank);
        if (ranked) {
            ++(e->rank);
        }
        canonical = e;
        u.emplace_back(this, ranked);
    }
};

class type_variable : public type_expression {
    friend class heap;
    type_variable(string const name) : name(move(name)) {}

public:
    string const name;

    virtual void accept(class type_visitor *v) override;
};

class type_atom : public type_expression {
    friend class heap;

protected:
    type_atom(string const value) : value(move(value)) {}

public:
    string const value;

    virtual void accept(class type_visitor *v) override;
};

/*
class type_integer : public type_expression {
    friend class heap;
    type_integer(int const value) : value(move(value)) {}

public:
    int const value;
    virtual void accept(class type_visitor *v) override;
};
*/

class type_struct : public type_expression {
    friend class heap;
    template <typename T>
    type_struct(type_atom* const functor, T&& args)
        : functor(functor), args(forward<T>(args)) {}

public:
    type_atom* const functor;
    vector<type_expression*> const args;

    virtual void accept(class type_visitor *v) override;
};

/*
class type_conjunction : public type_expression {
    friend class heap;
    type_conjunction(
        vector<type_struct*>::iterator fl, vector<type_struct*>::iterator ll,
        vector<type_struct*>::iterator fr, vector<type_struct*>::iterator lr
    ) : fl(fl), ll(ll), fr(fr), lr(lr) {}

public:
    vector<type_struct*>::iterator fl, ll, fr, lr;
    virtual void accept(class type_visitor *v) override;
};
*/

class type_clause : public type_expression {
    friend class heap;

public:
    template <typename T, typename U>
    type_clause(type_struct *head, T&& cyck, U&& impl)
        : head(head), cyck(forward<T>(cyck)), impl(forward<U>(impl)) {}

    type_struct *const head;
    set<type_variable*> const cyck;
    vector<type_struct*> const impl;

    virtual void accept(class type_visitor *v) override;
};

class type_source : public type_expression {
    friend class heap;

public:
    type_source(source *const s) : src(s) {}
    unique_ptr<source> const src;
    //source* const src;

    virtual void accept(class type_visitor *v) override;
};

struct type_visitor {
    virtual void visit(type_variable *t) = 0;
    virtual void visit(type_atom *t) = 0;
    virtual void visit(type_struct *t) = 0;
    virtual void visit(type_clause *t) = 0;
    virtual void visit(type_source *t) = 0;
};

void type_variable::accept(class type_visitor *v) {v->visit(this);}
void type_atom::accept(class type_visitor *v) {v->visit(this);}
void type_struct::accept(class type_visitor *v) {v->visit(this);}
void type_clause::accept(class type_visitor *v) {v->visit(this);}
void type_source::accept(class type_visitor *v) {v->visit(this);}

//----------------------------------------------------------------------------
// Heap : The Global Stack

class heap {
    vector<unique_ptr<ast>> region;

public: 
    heap() {};
    heap(const heap&) = delete;
    heap(heap&&) = default;
    heap& operator= (const heap&) = delete;

    int checkpoint() {
        return region.size();
    }

    void backtrack(int p) {
        while (region.size() > p) {
            region.pop_back();
        }
    }

    // Types
    type_variable* new_type_variable(string const& n) {
        unique_ptr<type_variable> u(new type_variable(n));
        type_variable *const t = u.get();
        region.emplace_back(move(u));
        return t;
    }

    type_atom* new_type_atom(string const& value) {
        unique_ptr<type_atom> u(new type_atom(value));
        type_atom *const t = u.get();
        region.emplace_back(move(u));
        return t;
    }

    template <typename T>
    type_struct* new_type_struct(type_atom* const functor, T&& args) {
        unique_ptr<type_struct> u(new type_struct(functor, forward<T>(args)));
        type_struct *const t = u.get();
        region.emplace_back(move(u));
        return t;
    }

    template <typename T, typename U>
    type_clause* new_type_clause(type_struct *head, T&& cyck, U&& goals) {
        unique_ptr<type_clause> u(new type_clause(head, forward<T>(cyck), forward<U>(goals)));
        type_clause *const t = u.get();
        region.emplace_back(move(u));
        return t;
    }

    type_source* new_type_source(source *src) {
        unique_ptr<type_source> u(new type_source(src));
        type_source *const t = u.get();
        region.emplace_back(move(u));
        return t;
    }
};

//----------------------------------------------------------------------------
// Show Type Graph - assumes no cycles

class var_map {
    typedef map<type_variable*, int> map_type;
    typedef map<string, int> map_name;
    map_type tmap;
    map_name nmap;

public:
    void clear() {
        tmap.clear();
        nmap.clear();
    }

    int get(type_variable *t) {
        map_type::iterator const i = tmap.find(t);
        if (i == tmap.end()) {
            map_name::iterator const j = nmap.find(t->name);
            int id = 1;
            if (j == nmap.end()) {
                nmap[t->name] = id;
            } else {           
                id = ++(j->second);
            }
            tmap[t] = id;
            return id;
        } else {
            return i->second;
        }
    }
};

class type_show : public type_visitor {
    var_map tvar_map;
    bool debug;

    void show_variable(type_variable *const t) {
        int const x {tvar_map.get(t)};
        stringstream ss;
        ss << t->name << x;
        cout << ss.str();
    }

public:
    virtual void visit(type_variable *const t) override {
        show_variable(t);
    }

    virtual void visit(type_atom *const t) override {
        cout << t->value;
    }

    virtual void visit(type_struct *const t) override {
        cout << t->functor->value;
        if (t->args.size() > 0) {
            cout << "(";
            for (auto i = t->args.begin(); i != t->args.end(); ++i) {
                find(*i)->accept(this);
                if (i + 1 != t->args.end()) {
                    cout << ", ";
                }
            }
            cout << ")";
        }
    }

    virtual void visit(type_clause *const t) override {
        t->head->accept(this);
        if (t->cyck.size() > 0) {
            cout << " [";
            for (set<type_variable*>::iterator i = t->cyck.begin(); i != t->cyck.end();) {
                show_variable(*i);
                ++i;
                if (i != t->cyck.end()) {
                    cout << ", ";
                }
            }
            cout << "] ";
        }
        if (t->impl.size() > 0) {
            cout << " :- ";
            for (auto i = t->impl.begin(); i != t->impl.end(); ++i) {
                find(*i)->accept(this);
                if (i + 1 != t->impl.end()) {
                    cout << ", ";
                }
            }
        }
    }

    virtual void visit(type_source *const t) override {
        cout << "<source: " << t->src.get() << ">";
    }

    explicit type_show(bool debug = false) : debug(debug) {}

    void operator() (type_expression *const t) {
        if (t != nullptr) {
            find(t)->accept(this);
        }
    }

    template <typename T> void range(typename T::const_iterator const begin, typename T::const_iterator const end) {
        for (typename T::const_iterator i = begin; i != end; ++i) {
            operator() (*i);
            if (i + 1 != end) {
                cout << ", ";
            }
        }
    }

    void reset() {
        tvar_map.clear();
    }
};

//----------------------------------------------------------------------------
// Get Vars - assumes no cycles

class get_variables : public type_visitor {
    typedef set<type_variable*> tvars_type;

    tvars_type tvars;

public:
    virtual void visit(type_variable *const t) override {
        tvars.insert(t);
    }

    virtual void visit(type_atom *const t) override {}

    virtual void visit(type_struct *const t) override {
        for (type_expression *const u : t->args) {
            find(u)->accept(this);
        }
    }

    virtual void visit(type_clause *const t) override {
        find(t->head)->accept(this);
        for (type_struct *const u : t->impl) {
            find(u)->accept(this);
        }
    }

    virtual void visit(type_source *const t) override {}

    vector<type_expression*> operator() (vector<type_struct *> const ts) {
        tvars.clear();
        for (auto const &t : ts) {
            find(t)->accept(this);
        }
        vector<type_expression*> args;
        args.assign(tvars.begin(), tvars.end());
        return move(args);
    }
};

//----------------------------------------------------------------------------
// Instantiate Type - assumes no cycles

class type_instantiate : public type_visitor {
    typedef map<type_variable*, type_variable*> tvar_map_type;

    heap& ast;
    tvar_map_type tvar_map;
    type_expression *exp;

    type_struct* inst_struct(type_struct *const t) {
        vector<type_expression*> args;
        for (type_expression *const e : t->args) {
            find(e)->accept(this);
            args.push_back(exp);
        }
        return ast.new_type_struct(t->functor, move(args));
    }

public:
    type_clause* inst_rule(type_clause *const t) {
        tvar_map.clear();
        type_struct *const head = inst_struct(t->head);
        set<type_variable*> cyck;
        for (type_variable *const v : t->cyck) {
            cyck.insert(tvar_map.find(v)->second);
        }
        vector<type_struct*> impl;
        for (type_struct *const s : t->impl) {
            impl.push_back(inst_struct(s));
        }
        return ast.new_type_clause(head, move(cyck), move(impl));
    }
    
    virtual void visit(type_variable *const t) override {
        tvar_map_type::iterator const i = tvar_map.find(t);
        if (i == tvar_map.end()) { // fresh type variable
            type_variable *const n = ast.new_type_variable(t->name);
            tvar_map.emplace(t, n);
            exp = n;
        } else { // var in local scope
            exp = i->second;
        }
    }

    virtual void visit(type_atom *const t) override {
        exp = t;
    }

    virtual void visit(type_struct *const t) override {
        exp = inst_struct(t);
    }

    virtual void visit(type_clause *const t) override {
        exp = inst_rule(t);
    }

    virtual void visit(type_source *const t) override {}

    explicit type_instantiate(heap& ast) : ast(ast) {}

    type_expression* operator() (type_expression *const t) {
        tvar_map.clear();
        find(t)->accept(this);
        return exp;
    }
};

//----------------------------------------------------------------------------
// Cycle Check

class no_cycles : public type_visitor {
    set<type_expression*> visited;
    bool cycle_free;

    void check_struct(type_struct *const t) {
        pair<set<type_expression*>::const_iterator, bool> p = visited.insert(t);
        if (p.second) { // new element
            for (type_expression *const e : t->args) {
                find(e)->accept(this);
            }
            visited.erase(p.first);
        } else {
            cycle_free = false;
        }
    }

public:
    virtual void visit(type_variable *const t) override {}

    virtual void visit(type_atom *const t) override {}

    virtual void visit(type_struct *const t) override {
        check_struct(t);
    }

    virtual void visit(type_clause *const t) override {
        check_struct(t->head);
    }
    
    virtual void visit(type_source *const t) override {}

    bool operator() (type_expression *const t) {
        visited.clear();
        cycle_free = true;
        find(t)->accept(this);
        if (cycle_free == false) {
            cout << "CYCLIC ";
        }
        return cycle_free;
    }
};

//----------------------------------------------------------------------------
// Rational Tree Unification

class trail : public type_visitor {
    typedef pair<type_expression*, type_expression*> texp_pair;
    no_cycles nocyc;

    union_stack unions;
    set<texp_pair> done;
    vector<texp_pair> todo;

    type_expression *u2;
    bool unifies;
    
    inline void queue(type_expression *const t1, type_expression *const t2) {
        if (t1 != t2) {
            todo.emplace_back(t1, t2);
        }
    }

    void struct_struct(type_struct *const t1, type_struct *const t2) {
        if ((t1->functor == t2->functor) && (t1->args.size() == t2->args.size())) {
            if (done.emplace(t1, t2).second) {
                for (int i = 0; i < t1->args.size(); ++i) {
                    queue(t1->args[i], t2->args[i]);
                }
            } else {
                cout << "CYCLIC-UNIFICATION ";
            }
        } else {
            unifies = false;
        }
    }

public:
    class variable_unify : public type_visitor {
        trail &unify;
        type_variable *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            link(t1, t2, unify.unions);
        }
        virtual void visit(type_atom *const t2) override {
            t1->replace_with(t2, unify.unions);
        }
        virtual void visit(type_struct *const t2) override {
            t1->replace_with(t2, unify.unions);
        }
        virtual void visit(type_clause *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_source *const t2) override {
            t1->replace_with(t2, unify.unions);
        }
        explicit variable_unify(trail &unify) : unify(unify) {}
        void operator() (type_variable *const v1) {
            t1 = v1;
            unify.u2->accept(this);
        }
    } variable;

    virtual void visit(type_variable *const u1) override {
        variable(u1);
    }



    class atom_unify : public type_visitor {
        trail &unify;
        type_atom *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            t2->replace_with(t1, unify.unions);
        }
        virtual void visit(type_atom *const t2) override {
            if (t1->value != t2->value) {
                unify.unifies = false;
            }
        }
        virtual void visit(type_struct *const t2) override {
            if (t2->args.size() > 0 || t1->value != t2->functor->value) {
                unify.unifies = false;
            }
        }
        virtual void visit(type_clause *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_source *const t2) override {
            unify.unifies = false;
        }
        explicit atom_unify(trail &unify) : unify(unify) {}
        void operator() (type_atom *const v1) {
            t1 = v1;
            unify.u2->accept(this);
        }
    } atom;

    virtual void visit(type_atom *const u1) override {
        atom(u1);
    }



    class struct_unify : public type_visitor {
        trail &unify;
        type_struct *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            t2->replace_with(t1, unify.unions);
        }
        virtual void visit(type_atom *const t2) override {
            if (t1->args.size() > 0 || t2->value != t1->functor->value) {
                unify.unifies = false;
            }
        }
        virtual void visit(type_struct *const t2) override {
            unify.struct_struct(t1, t2);
        }
        virtual void visit(type_clause *const t2) override {
            unify.queue(t1, t2->head);
        }
        virtual void visit(type_source *const t2) override {
            unify.unifies = false;
        }
        explicit struct_unify(trail &unify) : unify(unify) {}
        void operator() (type_struct *const a1) {
            t1 = a1;
            unify.u2->accept(this);
        }
    } strct;

    virtual void visit(type_struct *const u1) override {
        strct(u1);
    }



    class rule_unify : public type_visitor {
        trail &unify;
        type_clause *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_atom *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_struct *const t2) override {
            unify.queue(t1->head, t2);
        }
        virtual void visit(type_clause *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_source *const t2) override {
            unify.unifies = false;
        }
        explicit rule_unify(trail &unify) : unify(unify) {}
        void operator() (type_clause *const r1) {
            t1 = r1;
            unify.u2->accept(this);
        }
    } rule;


    virtual void visit(type_clause *const u1) override {
        rule(u1);
    }



    class source_unify : public type_visitor {
        trail &unify;
        type_source *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            t2->replace_with(t1, unify.unions);
        }
        virtual void visit(type_atom *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_struct *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_clause *const t2) override {
            unify.unifies = false;
        }
        virtual void visit(type_source *const t2) override {
            if (t1->src != t2->src) {
                unify.unifies = false;
            }
        }
        explicit source_unify(trail &unify) : unify(unify) {}
        void operator() (type_source *const r1) {
            t1 = r1;
            unify.u2->accept(this);
        }
    } source;

    virtual void visit(type_source *const u1) override {
        source(u1);
    }



    explicit trail() : variable(*this), atom(*this), strct(*this),
        rule(*this), source(*this) {}

    bool unify() {
        unifies = true;

        while (todo.size() > 0 && unifies) {
            texp_pair const &tt = todo.back();
            type_expression *const u1 = find(tt.first);
            u2 = find(tt.second);
            todo.pop_back();
            if (u1 != u2) {
                u1->accept(this);
            }
        }

        return unifies;
    }

    bool unify_exp_exp(type_expression *const x, type_expression *const y) {
        done.clear();
        todo.clear();
        todo.push_back(make_pair(x, y));

        /*type_show ts;
        ts(x);
        cout << " <U> ";
        ts(y);
        cout << "\n";*/

        return unify();
    }

    bool unify_goal_rule(type_struct *const g, type_clause *const r) {
        done.clear();
        todo.clear();
        struct_struct(g, r->head);

        /*type_show ts;
        ts(g);
        cout << " <U> ";
        ts(r);
        cout << "\n";*/

        bool unifies = unify();

        if (unifies) {
            for (type_variable *const v : r->cyck) {
                if (!nocyc(v)) {
                    return false;
                }
            }

            /*cout << " = ";
            ts(g); 
            cout << " <U> ";
            ts(r);
            cout << "\n\n";*/

            return true;
        }

        return false;
    }

    int checkpoint() {
        return unions.size();
    }

    void backtrack(int const p) {
        while(unions.size() > p) {
            pair<type_expression *const, bool const> &u = unions.back();
            u.first->deunion(u.second);
            unions.pop_back();
        }
    }

    bool match_goal_rule(type_struct *const g, type_clause *const r) {
        //cout << "MATCH: ";
        int const p = checkpoint();
        bool const matches = unify_goal_rule(g, r);
        backtrack(p);
        return matches;
    }
};

//----------------------------------------------------------------------------
// Unfolding:
// (A0 :- A1, A2,..., An) (+) (B0 :- B1, B2,..., Bm) = mgu(A1, B0) * (A0 :- B1,..., Bm, A2,..., An)

struct context {
    atoms &names;
    env_type &env;
    heap ast;
    trail unify;
    type_instantiate inst;
    vector<type_atom*> N;
    vector<type_atom*> P;

    context(atoms &names, env_type &env)
        : names(names), env(env), inst(ast) {}
    context(const context&) = default;
    context& operator=(const context&) = default;
};

class unfolder : public source {
    static string const builtin_answer_source;
    static string const builtin_get;
    static string const builtin_stop;
    static string const builtin_true;
    static string const builtin_false;
    // builtin_unknown is unsound.

    context &cxt;
    type_clause *fresh;
    type_clause *goal;
    vector<type_clause*>::iterator begin;
    vector<type_clause*>::iterator end;
    int const trail_checkpoint;
    int const env_checkpoint;
    bool found;

public:
    unfolder(const unfolder&) = delete;
    unfolder(unfolder&&) = default;
    unfolder& operator= (const unfolder&) = delete;

    unfolder(context &cxt, type_clause *g)
    : cxt(cxt)
    , goal(g)
    , begin()
    , end()
    , trail_checkpoint(cxt.unify.checkpoint())
    , env_checkpoint(cxt.ast.checkpoint()) {
        type_struct *first = goal->impl.front();
        env_type::iterator i = cxt.env.find(first->functor);
        if (i != cxt.env.end()) {
            begin = i->second.begin();
            end = i->second.end();
            found = true;
        } else {
            found = false;
        }
    }

    virtual type_clause* get() override;

    virtual type_clause* reget() override {
        return goal;
    }

    virtual bool at_end() override {
        return begin == end;
    }
};

//----------------------------------------------------------------------------
// Transitive Closure

class solver : public source {
    static int next_id;
    int const id;

    context cxt;
    int const trail_checkpoint;
    int const env_checkpoint;
    vector<unique_ptr<source>> or_stack;

public:
    solver(const solver&) = delete;
    solver(solver&&) = default;
    solver& operator= (const solver&) = delete;

    solver(atoms &names, env_type &env, type_clause *goal) 
    : id(++next_id)
    , cxt(names, env)
    , trail_checkpoint(cxt.unify.checkpoint())
    , env_checkpoint(cxt.ast.checkpoint()) {
        profile p;
        or_stack.emplace_back(new unfolder(cxt, goal));
        //cout << "SOLVER " << id << " CONS\n";
    }

    ~solver() override {
        //cout << "SOLVER " << id << " DEST\n";
        stop();
    }

    type_clause *next_goal;

    type_clause* get() override {
        profile p;
        //cout << "SOLVER GET\n";
        while (!or_stack.empty()) {
            source &src = *(or_stack.back());
            next_goal = src.get();
            //cout << "SOLVER GOT\n";
            if (next_goal != nullptr) {
                //cout << "SUCC\n";
                if (next_goal->impl.empty()) {
                    cout << "PROOF:\n";
                    type_show ts;
                    for (auto i = or_stack.begin(); i != or_stack.end(); ++i) {
                        if ((*i)->reget()->impl.size() > 0) {
                            ts((*i)->reget()->impl.front());
                        }
                        cout << "\n";
                    }
                    return next_goal;
                }
                //if (src.at_end()) { // LCO
                //    or_stack.pop_back();
                    //cout << "[" << or_stack.size() << "] LCO\n";
                //}
                or_stack.emplace_back(new unfolder(cxt, next_goal));
            } else {
                //cout << "FAIL\n";
                or_stack.pop_back(); 
                //cout << "[" << or_stack.size() << "]\n";
                while (!or_stack.empty() && or_stack.back()->at_end()) {
                    or_stack.pop_back();
                }
            }
        }
        or_stack.clear();
        cxt.unify.backtrack(trail_checkpoint);
        cxt.ast.backtrack(env_checkpoint);
        next_goal = cxt.ast.new_type_clause(
            cxt.ast.new_type_struct(cxt.names.find("np")->second, vector<type_expression*> {}),
            set<type_variable*> {},
            vector<type_struct*> {}
        );
        return next_goal;
    }

    virtual void stop() override {
        //cout << "SOLVER " << id << " STOP\n";
        or_stack.clear();
        cxt.unify.backtrack(trail_checkpoint);
        cxt.ast.backtrack(env_checkpoint);
    }

    type_clause* reget() override {
        return next_goal;
    }

    virtual bool at_end() override {
        return or_stack.empty();
    }
};

int solver::next_id = 0;

//----------------------------------------------------------------------------
// Unfolder::get 

type_clause* unfolder::get() {
    cxt.unify.backtrack(trail_checkpoint);
    cxt.ast.backtrack(env_checkpoint);
    type_struct *const first = goal->impl.front();
    //cout << "UNFOLDER GET\n";
    
    //if (!found) {
        // any builtins...
    //}

    while (found && (begin != end)) {
        type_clause *const clause = *(begin++);
        if (cxt.unify.match_goal_rule(first, clause)) {
            //cout << "MATCH\n";
            fresh = cxt.inst.inst_rule(clause);
            cxt.unify.unify_goal_rule(first, fresh);
            vector<type_struct*> impl(fresh->impl.begin(), fresh->impl.end());
            impl.insert(impl.end(), goal->impl.begin() + 1, goal->impl.end());
            /*type_show ts;
            cout << "\nIMPL:\n";
            for (auto i = goal->impl.begin(); i != goal->impl.end(); ++i) {
                ts(*i);
                cout << "\n";
            }*/
            //cout <<"\n";
            return cxt.ast.new_type_clause(goal->head, goal->cyck, move(impl));
        } /*else {
            cout << "NO MATCH\n";
        }*/
    }
    //cout << "EMPTY\n";
    return nullptr;
}

//----------------------------------------------------------------------------
// Parser 

is_char is_brace_open('(');
is_char is_brace_close(')');
is_char is_dot('.');
is_char is_comma(',');
is_char is_colon(':');
is_char is_minus('-');
is_char is_hash('#');
is_char is_cr('\r');
is_char is_nl('\n');
is_char is_eof(EOF);
is_char is_underscore('_');
is_either<struct is_alnum, is_char> is_name1(is_alnum, is_underscore);
is_either<is_char, is_char> is_nl_or_eof(is_nl, is_eof);
is_not<is_either<is_char, is_char>> not_nl_or_eof(is_nl_or_eof);

// Logic Parser --------------------------------------------------------------

class term_parser : public fparse {
    type_show show_type;
    heap& ast;
    set<type_variable*> repeated;
    map<string, type_variable*> vmap;

    atoms names = {
        make_pair("np", ast.new_type_atom("np")),
        make_pair("the", ast.new_type_atom("the"))
    };

public:
    type_variable* variable() {
        string n;
        expect(is_upper, &n);
        while (accept(is_alnum, &n));
        space();
        map<string, type_variable*>::iterator i = vmap.find(n);
        if (i == vmap.end()) {
            type_variable *v = ast.new_type_variable(n);
            vmap.insert(make_pair(n, v));
            return v;
        } else {
            repeated.insert(i->second);
            return i->second;
        }
    }

    type_atom* atom() {
        string a;
        expect(is_lower, &a);
        while (accept(is_name1, &a));
        space();
        auto const i = names.find(a);
        if (i == names.end()) {
            type_atom *t = ast.new_type_atom(a);
            names.insert(make_pair(a, t));
            return t;
        } else {
            return i->second;
        }
    }

    type_expression* term() {
        if (test(is_upper)) {
            return variable();
        } if (test(is_lower)) {
            type_atom* a = atom();
            if (accept(is_brace_open)) {
                vector<type_expression*> terms = parse_terms();
                expect(is_brace_close);
                return ast.new_type_struct(a, move(terms));
            } else {
                return a;
            }
        } else {
            error("Term parser expected", "Variable or Term");
            throw;
        }
    }

    vector<type_expression*> parse_terms() {
        vector<type_expression*> args {};
        do {
            space();
            args.push_back(term());
            space();  
        } while (accept(is_comma));
        return move(args);
    }

    type_struct* parse_struct() {
        type_atom* functor = atom();
        if(accept(is_brace_open)) {
            vector<type_expression*> terms {parse_terms()};
            expect(is_brace_close);
            space();
            return ast.new_type_struct(functor, move(terms));
        } else {
            space();
            return ast.new_type_struct(functor, vector<type_expression*> {});
        } 
    }

    vector<type_struct*> parse_structs() {
        vector<type_struct*> ss;
        do {
            space();
            ss.push_back(parse_struct());
        } while (accept(is_comma));
        space();
        return move(ss);
    }

    type_clause* parse_rule() {
        type_struct *head = nullptr;
        set<type_variable*> cyck {};
        vector<type_struct*> impl {};

        repeated.clear();
        if (!test(is_colon)) {
            head = parse_struct();
            cyck = repeated;
        }
        if (accept(is_colon)) {
            expect(is_minus);
            impl = parse_structs();
        } 
        expect(is_dot);
        return ast.new_type_clause(head, move(cyck), move(impl));
    }

    explicit term_parser(heap &ast) : ast(ast) {}

    void operator() (fstream *f) {
        env_type env;
        vector<vector<type_struct*>> goals;

        set_fstream(f);
        do {
            space();
            if (accept(is_hash)) {
                while(accept(not_nl_or_eof));
            } else {
                type_clause *r = parse_rule();
                if (r->head == nullptr) {
                    goals.push_back(r->impl);
                } else {
                    env_type::iterator const i = env.find(r->head->functor);
                    if (i == env.end()) {
                        env.emplace(r->head->functor, vector<type_clause*> {r});
                    } else {
                        i->second.push_back(r);
                    }
                }
            }
            space();
            vmap.clear();
        } while (!accept(is_eof));

        /* 
        for (auto const& fun : env) {
            for (auto const& c : fun.second) {
                show_type(c);
                cout << "\n";
            }
        }
        cout << "\n";
        */

        get_variables gv;
        type_expression *answer;
        //int const count = 100;
        int const count = 1;
        context cxt(names, env);
        for (vector<type_struct*> &goal : goals) {
            for (int i = 0; i < count; ++i) {
                solver solve(names, env, ast.new_type_clause(ast.new_type_struct(
                    ast.new_type_atom("the"), gv(goal)), set<type_variable*> {}, goal));
                //solver2 solve(ast, env, ast.new_type_clause(ast.new_type_struct("goal", gv(goal)), set<type_variable*> {}, goal));
                answer = solve.get();
                if (i + 1 < count) {
                    solve.stop();
                } else {
                    if (answer != nullptr) {
                        cout << "ELAPSED TIME: " << profile::report() / static_cast<double>(count) << "us\n";
                        //cout << "YES\n\n";
                        show_type(answer);
                        cout << "\n\n";
                    } else {
                        cout << "ELAPSED TIME: " << profile::report() / static_cast<double>(count) << "us\n";
                        //cout << "NP\n\n";
                        cout << "ERROR\n\n";
                    }
                }
            }
        }
    }
};

//----------------------------------------------------------------------------

int main(int argc, char const *const *argv) {
    if (argc < 1) {
        printf("no input files.\n");
    } else {
        for (int i(1); i < argc; ++i) {
            try {
                heap ast;
                term_parser parse(ast);
                type_show show_type;

                fstream in(argv[i], ios_base::in);
                if (in.is_open()) {
                    parse(&in); // FIXME return and execute
                    in.close();
                } else {
                    cerr << "could not open " << argv[i] << "\n";
                    return 1;
                }
            } catch (parse_error& e) {
                cerr << argv[i] << ": " << e.what()
                    << " '" << e.exp
                    << "' found '" << static_cast<char>(e.sym)
                    << "' at line " << e.row
                    << ", column " << e.col << "\n";
                return 2;
            }
        }
    }
}
