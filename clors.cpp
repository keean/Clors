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
#include <cassert>

extern "C" {
#include <sys/resource.h>
}

#ifdef DEBUG
#define IF_DEBUG(X) X
#else
#define IF_DEBUG(X)
#endif

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
    static int depth;

public:
    depth_profile(int const i) {
        depth = i;
        profile::start();
    }
    ~depth_profile() {
        profile::finish();
    }
    static int report() {
        return depth;
    }
};

int depth_profile::depth;

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
class type_attrvar;
class type_atom;
class type_struct;
class type_clause;

using env_type = map<type_atom*, vector<type_clause*>>;
using atoms = map<string, type_atom*>;

//----------------------------------------------------------------------------
// Expression Graph

struct ast {
    virtual ~ast() {};
};

using union_stack = vector<pair<type_expression *const, bool const>>;

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

    friend void link2(type_attrvar*& x, type_attrvar*& y, union_stack& u);

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

    template <typename T>
    type_variable(T&& name) : name(forward<T>(name)) {}

public:
    string const name;

    virtual void accept(class type_visitor *v) override;
};

class type_attrvar : public type_expression {
    friend class heap;

    type_attrvar(type_variable* var, type_struct* goal) : var(var), goal(goal), next(nullptr) {}

public:
    type_variable* const var;
    type_struct* const goal;
    type_attrvar* next;

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

class type_struct : public type_expression {
    friend class heap;
    template <typename T>
    type_struct(type_atom* const functor, T&& args, bool neg)
        : functor(functor), args(forward<T>(args)), negated(neg) {}

public:
    type_atom* const functor;
    vector<type_expression*> const args;
    bool const negated;

    virtual void accept(class type_visitor *v) override;
};

class type_clause : public type_expression {
    friend class heap;

public:
    template <typename T, typename U>
    type_clause(type_struct *head, T&& cyck, U&& impl, int id)
        : head(head), cyck(forward<T>(cyck)), impl(forward<U>(impl)), id(id) {}

    int const id;
    type_struct *const head;
    set<type_variable*> const cyck;
    vector<type_struct*> const impl;

    virtual void accept(class type_visitor *v) override;
};



struct type_visitor {
    virtual void visit(type_variable *t) = 0;
    virtual void visit(type_attrvar *t) = 0;
    virtual void visit(type_atom *t) = 0;
    virtual void visit(type_struct *t) = 0;
    virtual void visit(type_clause *t) = 0;
};

void type_variable::accept(class type_visitor *v) {v->visit(this);}
void type_attrvar::accept(class type_visitor *v) {v->visit(this);}
void type_atom::accept(class type_visitor *v) {v->visit(this);}
void type_struct::accept(class type_visitor *v) {v->visit(this);}
void type_clause::accept(class type_visitor *v) {v->visit(this);}

void link2(type_attrvar*& x, type_attrvar*& y, union_stack& u) {
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
    template <typename T>
    type_variable* new_type_variable(T&& n) {
        type_variable *const t = new type_variable(n);
        region.emplace_back(t);
        return t;
    }

    type_attrvar* new_type_attrvar(type_variable* v, type_struct* g) {
        type_attrvar* const t = new type_attrvar(v, g);
        region.emplace_back(t);
        return t;
    }

    type_atom* new_type_atom(string const& value) {
        type_atom *const t = new type_atom(value);
        region.emplace_back(t);
        return t;
    }

    template <typename T>
    type_struct* new_type_struct(type_atom* const functor, T&& args, bool neg) {
        type_struct *const t = new type_struct(functor, forward<T>(args), neg);
        region.emplace_back(t);
        return t;
    }

    template <typename T = set<type_variable*>, typename U = vector<type_struct*>>
    type_clause* new_type_clause(type_struct *head
    , T&& cyck = set<type_variable*> {}, U&& goals = vector<type_struct*> {}
    , int id = 0) {
        type_clause *const t = new type_clause(head, forward<T>(cyck), forward<U>(goals), id);
        region.emplace_back(t);
        return t;
    }
};

//----------------------------------------------------------------------------
// Show Type Graph - assumes no cycles

class var_map {
    using map_type = map<type_variable*, int>;
    using map_name = map<string, int>;
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
    bool top;
    bool constraint;

    void show_variable(type_variable *const t) {
        int const x {tvar_map.get(t)};
        stringstream ss;
        ss << t->name << x;
        cout << ss.str();
    }

    void show_struct(type_struct *const t) {
        if (t->negated) {
            cout << "-";
        }
        cout << t->functor->value;
        if (t->args.size() > 0) {
            cout << "(";
            for (auto i = t->args.begin(); i != t->args.end(); ++i) {
                (*i)->accept(this);
                if (i + 1 != t->args.end()) {
                    cout << ", ";
                }
            }
            cout << ")";
        }
    }

public:
    virtual void visit(type_variable *const t) override {
        if (top) {
            top = false;
            show_variable(t);
            type_expression *const e = find(t);
            if (t != e) {
                cout << " = ";
                e->accept(this);
            }
            top = true;
        } else {
            type_expression *const e = find(t);
            if (t != e) {
                e->accept(this);
            } else {
                show_variable(t);
            }
        }
    }

    virtual void visit(type_attrvar *const t) override {
        show_variable(t->var);
        if (!constraint && t->goal != nullptr) {
            constraint = true;
            cout << "{";
            int j = 0;
            for (auto i = t; i != nullptr; i = i->next) {
                ++j;
                assert(i->goal != nullptr);
                show_struct(i->goal);
                if (i->next != nullptr) {
                    cout << ", ";
                }
            }
            cout << "} ";
            constraint = false;
        }
    }

    virtual void visit(type_atom *const t) override {
        cout << t->value;
    }

    virtual void visit(type_struct *const t) override {
        show_struct(t);
    }

    virtual void visit(type_clause *const t) override {
        cout << t->id << ".\t";
        show_struct(t->head);
        IF_DEBUG(
            if (t->cyck.size() > 0) {
                cout << " [";
                for (set<type_variable*>::iterator i = t->cyck.begin(); i != t->cyck.end();) {
                    show_variable(*i);
                    ++i;
                    if (i != t->cyck.end()) {
                        cout << ", ";
                    }
                }
                cout << "]";
            }
        )
        if (t->impl.size() > 0) {
            cout << " :-\n";
            for (auto i = t->impl.begin(); i != t->impl.end(); ++i) {
                cout << "\t";
                show_struct(*i);
                if (i + 1 != t->impl.end()) {
                    cout << ",\n";
                }
            }
        }
    }

    explicit type_show(bool debug = false) : debug(debug) {}

    void operator() (type_expression *const t) {
        if (t != nullptr) {
            constraint = false;
            top = true;
            t->accept(this);
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
// Test if term is ground - assumes no cycles.

class is_ground : public type_visitor {
    vector<type_expression*> todo;
    enum result {none, variable, attributed} result;
    type_variable* var;
    type_attrvar* attr;

    virtual void visit(type_variable* const t) override {
        var = t;
        result = variable;
    }

    virtual void visit(type_attrvar* const t) override {
        attr = t;
        result = attributed;
    }

    virtual void visit(type_atom* const t) override {}

    virtual void visit(type_struct* const t) override {
        for (type_expression *const u : t->args) {
            todo.push_back(u);
        }
    }

    virtual void visit(type_clause* const t) override {
        todo.push_back(t->head);
        for (type_struct* const u : t->impl) {
            todo.push_back(t);
        }
    }

    enum result operator() (type_expression* const t) {
        result = none;
        todo.clear();
        todo.push_back(t);

        while ((!todo.empty()) && (result == none)) {
            type_expression* const u = find(todo.back());
            todo.pop_back();
            find(u)->accept(this);
        }

        return result;
    }
};
        
//----------------------------------------------------------------------------
// Get Vars - assumes no cycles

class get_variables : public type_visitor {
    using tvars_type = set<type_variable*>;

    tvars_type tvars;

public:
    virtual void visit(type_variable *const t) override {
        tvars.insert(t);
    }

    virtual void visit(type_attrvar *const t) override {
        tvars.insert(t->var);
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
    using tvar_map_type = map<type_variable*, type_variable*>;

    heap& ast;
    tvar_map_type tvar_map;
    type_expression *exp;

    type_struct* inst_struct(type_struct *const t) {
        vector<type_expression*> args;
        for (type_expression *const e : t->args) {
            find(e)->accept(this);
            args.push_back(exp);
        }
        return ast.new_type_struct(t->functor, move(args), t->negated);
    }

    type_variable* inst_var(type_variable *const t) {
        tvar_map_type::iterator const i = tvar_map.find(t);
        if (i == tvar_map.end()) { // fresh type variable
            type_variable *const n = ast.new_type_variable(t->name);
            tvar_map.emplace(t, n);
            return n;
        } 
        return i->second;
    }

    type_attrvar* inst_attr(type_attrvar* const t) {
        type_attrvar* const a = ast.new_type_attrvar(inst_var(t->var), inst_struct(t->goal));
        if (t->next != nullptr) {
            a->next = inst_attr(t->next);
        }
        return a;
    }

public:
    type_clause* inst_rule(
        type_struct *const h,
        set<type_variable*> const& c,
        vector<type_struct*> const& i,
        int d
    ) {
        tvar_map.clear();
        type_struct *const head = inst_struct(h);
        set<type_variable*> cyck;
        for (type_variable *const v : c) {
            tvar_map_type::const_iterator j = tvar_map.find(v);
            if (j != tvar_map.end()) {
                cyck.insert(j->second);
            }
        }
        vector<type_struct*> impl;
        for (type_struct *const s : i) {
            impl.push_back(inst_struct(s));
        }
        return ast.new_type_clause(head, move(cyck), move(impl), d);
    }

    virtual void visit(type_variable *const t) override {
        exp = inst_var(t);
    }

    virtual void visit(type_attrvar *const t) override {
        exp = inst_attr(t);
    }

    virtual void visit(type_atom *const t) override {
        exp = t;
    }

    virtual void visit(type_struct *const t) override {
        exp = inst_struct(t);
    }

    virtual void visit(type_clause *const t) override {
        exp = inst_rule(t->head, t->cyck, t->impl, t->id);
    }

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

    virtual void visit(type_attrvar *const t) override {}

    virtual void visit(type_atom *const t) override {}

    virtual void visit(type_struct *const t) override {
        check_struct(t);
    }

    virtual void visit(type_clause *const t) override {
        check_struct(t->head);
    }
    
    bool operator() (type_expression *const t) {
        visited.clear();
        cycle_free = true;
        find(t)->accept(this);
        //if (cycle_free == false) {
        //    cout << "CYCLIC ";
        //}
        return cycle_free;
    }
};

//----------------------------------------------------------------------------
// Rational Tree Unification

struct trail : public type_visitor {
    union_stack unions;

private:
    using texp_pair = pair<type_expression*, type_expression*>;
    no_cycles nocyc;

    vector<texp_pair> todo;
    vector<type_attrvar*> deferred_goals;

    type_expression *u2;
    bool unifies;
    
    inline void queue(type_expression *const t1, type_expression *const t2) {
        if (t1 != t2) {
            todo.emplace_back(t1, t2);
        }
    }

    inline void struct_struct(type_struct *const t1, type_struct *const t2) {
        if ((t1->functor == t2->functor) && (t1->args.size() == t2->args.size())) {
            link(t1, t2, unions);
            for (int i = 0; i < t1->args.size(); ++i) {
                queue(t1->args[i], t2->args[i]);
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
        virtual void visit(type_attrvar* const t2) override {
            unify.deferred_goals.push_back(t2);
            t1->replace_with(t2, unify.unions);
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
        explicit variable_unify(trail &unify) : unify(unify) {}
        void operator() (type_variable *const v1) {
            t1 = v1;
            unify.u2->accept(this);
        }
    } variable;

    virtual void visit(type_variable *const u1) override {
        variable(u1);
    }



    class attrvar_unify : public type_visitor {
        trail &unify;
        type_attrvar *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            unify.deferred_goals.push_back(t1);
            t2->replace_with(t1, unify.unions);
        }
        virtual void visit(type_attrvar* t2) override {
            //unify.deferred_goals.push_back(t1);
            //unify.deferred_goals.push_back(t2);
            link2(t1, t2, unify.unions);
            type_attrvar* i = t2;
            while (i->next != nullptr) {
                i = i->next;
            }
            i->next = t1;
        }
        virtual void visit(type_atom *const t2) override {
            unify.deferred_goals.push_back(t1);
            t1->replace_with(t2, unify.unions);
        }
        virtual void visit(type_struct *const t2) override {
            unify.deferred_goals.push_back(t1);
            t1->replace_with(t2, unify.unions);
        }
        virtual void visit(type_clause *const t2) override {
            unify.unifies = false;
        }
        explicit attrvar_unify(trail &unify) : unify(unify) {}
        void operator() (type_attrvar *const v1) {
            t1 = v1;
            unify.u2->accept(this);
        }
    } attrvar;

    virtual void visit(type_attrvar *const u1) override {
        attrvar(u1);
    }



    class atom_unify : public type_visitor {
        trail &unify;
        type_atom *t1;
    public:
        virtual void visit(type_variable *const t2) override {
            t2->replace_with(t1, unify.unions);
        }
        virtual void visit(type_attrvar *const t2) override {
            unify.deferred_goals.push_back(t2);
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
        virtual void visit(type_attrvar *const t2) override {
            unify.deferred_goals.push_back(t2);
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
        virtual void visit(type_attrvar *const t2) override {
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
        explicit rule_unify(trail &unify) : unify(unify) {}
        void operator() (type_clause *const r1) {
            t1 = r1;
            unify.u2->accept(this);
        }
    } rule;


    virtual void visit(type_clause *const u1) override {
        rule(u1);
    }

    explicit trail() : variable(*this), attrvar(*this), atom(*this), strct(*this),
        rule(*this) {}

private:
    void unify() { // set unifies to true first.
        while (todo.size() > 0 && unifies) {
            texp_pair const &tt = todo.back();
            type_expression *const u1 = find(tt.first);
            u2 = find(tt.second);
            todo.pop_back();
            if (u1 != u2) {
                u1->accept(this);
            }
        }
    }

public:
    bool exp_exp(type_expression *const x, type_expression *const y) {
        deferred_goals.clear();
        todo.clear();
        unifies = true;

        todo.push_back(make_pair(x, y));

        //type_show ts;
        //ts(x);
        //cout << " <U> ";
        //ts(y);
        //cout << "\n";

        unify();

        return unifies && nocyc(x) && nocyc(y);
    }

    bool unify_goal_rule(type_struct *const g, type_clause *const r) {
        deferred_goals.clear();
        todo.clear();
        unifies = true;

        struct_struct(g, r->head);

        /*type_show ts;
        ts(g);
        cout << " <U> ";
        ts(r);
        cout << endl;*/

        if (unifies) {
            unify();
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

    vector<type_attrvar*> const& get_deferred_goals() {
        return deferred_goals;
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
// Rational Tree Disunification: only result, no variables unified.

struct disunify : public type_visitor {
    enum result {different, same, variable_deferred, attrvar_deferred} result;
    vector<type_attrvar*> deferred_goals;
    type_variable* defer_variable;
    type_attrvar* defer_attrvar;

private:
    using texp_pair = pair<type_expression*, type_expression*>;
    vector<texp_pair> todo;
    type_expression *u2;

    inline void queue(type_expression *const t1, type_expression *const t2) {
        if (t1 != t2) {
            todo.emplace_back(t1, t2);
        }
    }

    inline void struct_struct(type_struct *const t1, type_struct *const t2) {
        if ((t1->functor == t2->functor) && (t1->args.size() == t2->args.size())) {
            //link(t1, t2, unions); // need this for cyclic termination? Don't think so as
            //the result of the previous unifications must have no cycles, and disunification
            //does not alter the type graph.
            for (int i = 0; i < t1->args.size(); ++i) {
                queue(t1->args[i], t2->args[i]);
            }
        } else {
            result = different;
        }
    }

    class atom_disunify : public type_visitor {
        disunify &du;
        type_atom *t1;
    public:
        virtual void visit(type_variable* const t2) override {du.defer_variable=t2; du.result = variable_deferred;}
        virtual void visit(type_attrvar* const t2) override {du.defer_attrvar=t2; du.result = attrvar_deferred;}
        /*virtual void visit(type_variable* const t2) override {t2->replace_with(t1, unify.unions);} //thaw??
        virtual void visit(type_attrvar* const t2) override {
            unify.deferred_goals.push_back(t2);
            t2->replace_with(t1, unify.unions);
        }*/
        virtual void visit(type_atom* const t2) override {du.result = different;}
        virtual void visit(type_struct* const t2) override {du.result = different;}
        virtual void visit(type_clause* const t2) override {du.result = different;} // need to think about heads and atoms?
        void operator() (type_atom* const u1) {
            t1 = u1;
            du.u2->accept(this);
        }
        atom_disunify(disunify &du) : du(du) {}
    } atom_disunify;

    class struct_disunify : public type_visitor {
        disunify &du;
        type_struct *t1;
    public:
        virtual void visit(type_variable* const t2) override {du.defer_variable=t2; du.result = variable_deferred;}
        virtual void visit(type_attrvar* const t2) override {du.defer_attrvar=t2; du.result = attrvar_deferred;}
        virtual void visit(type_atom* const t2) override {du.result = different;}
        virtual void visit(type_struct* const t2) override {du.struct_struct(t1, t2);}
        virtual void visit(type_clause* const t2) override {du.struct_struct(t1, t2->head);}
        void operator() (type_struct* const u1) {
            t1 = u1;
            du.u2->accept(this);
        }
        struct_disunify(disunify &du) : du(du) {}
    } struct_disunify;

    enum result du() {
        result = same;

        while ((todo.size() > 0) && (result == same)) {
            texp_pair const &tt = todo.back();
            type_expression *const u1 = find(tt.first);
            u2 = find(tt.second);
            todo.pop_back();

            type_show ts;
            ts(u1);
            cout << " <> ";
            ts(u2);
            cout << "\n";

            if (u1 != u2) {
                u1->accept(this);
            }
        }

        return result;
    }

public:
    virtual void visit(type_variable* const t1) override {defer_variable=t1; result = variable_deferred;}
    virtual void visit(type_attrvar* const t1) override {defer_attrvar=t1; result = attrvar_deferred;}
    virtual void visit(type_atom* const t1) override {atom_disunify(t1);}
    virtual void visit(type_struct* const t1) override {struct_disunify(t1);}
    virtual void visit(type_clause* const t1) override {struct_disunify(t1->head);}

    disunify() : atom_disunify(*this), struct_disunify(*this) {}

    enum result exp_exp(type_expression *const x, type_expression *const y) {
        todo.clear();
        todo.push_back(make_pair(x, y));

        type_show ts;
        ts(x);
        cout << " <D> ";
        ts(y);
        cout << "\n";

        return du();
    }

    type_variable* get_deferred_variable() {
        return defer_variable;
    }

    type_attrvar* get_deferred_attrvar() {
        return defer_attrvar;
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

    context(atoms &names, env_type &env)
        : names(names), env(env), inst(ast) {}
    context(const context&) = default;
    context& operator=(const context&) = default;
};

class unfolder {
    static vector<type_clause*> const invalid;

    context &cxt;
    type_clause *fresh;
    vector<type_clause*>::const_iterator begin;
    vector<type_clause*>::const_iterator end;
    int const trail_checkpoint;
    int const env_checkpoint;
    enum builtin {not_builtin, builtin_dif, builtin_duplicate_term} builtin;

public:
    type_clause *goal;
    int const depth;

    unfolder(const unfolder&) = delete;
    unfolder(unfolder&&) = default;
    unfolder& operator= (const unfolder&) = delete;

    unfolder(context &cxt, type_clause *g, int d)
    : cxt(cxt)
    , goal(g)
    , trail_checkpoint(cxt.unify.checkpoint())
    , env_checkpoint(cxt.ast.checkpoint())
    , builtin(not_builtin)
    , depth(d) {
        type_struct *first = goal->impl.front();
        env_type::iterator i = cxt.env.find(first->functor);
        if (i != cxt.env.end()) {
            begin = i->second.cbegin();
            end = i->second.cend();
        } else {
            end = invalid.cend();
            begin = end;

            if (first->functor->value == "dif" && first->args.size() == 2) {
                builtin = builtin_dif;
            } else if (first->functor->value == "duplicate_term" && first->args.size() == 2) {
                builtin = builtin_duplicate_term;
            }
        }
    }

    type_clause* get() {
        cxt.unify.backtrack(trail_checkpoint);
        cxt.ast.backtrack(env_checkpoint);
        type_struct *const first = goal->impl.front();

        //if (first->negated) { //need to swap goal-list and or stack for negated part
            //cout << "NEGATED" << endl;

            // -((a & b & c) | (d & e & f) | (g & h & i))
            // (-(a & b & c) & -(d & e & f) & -(g & h & i))
            // ((-a | -b | -c) & (-d | -e | -f) & (-g | -h | -i))

            // ((a | b | c) & (d | e | f) & (g | h | i)
            // (-(-a & -b & -c) & (-d & -e & -f) & (-g & -h & -i))
            // -((-a & -b & -c) | (-d & -e & -f) | (-g & -h & -i)
            // try each goal:

            /*while (begin != end) {
                type_clause* clause = *(begin++);
                if (cxt.unify.match_goal_rule(first, clause)) {
                    fresh = cxt.inst.inst_rule(clause->head, clause->cyck, clause->impl, clause->id);
                    cxt.unify.unify_goal_rule(first, fresh);



                switch( dis.exp_exp(first, fresh->head)) {
                    case disunify::same:
                        return nullptr;
                    case disunify::different:
                        break;
                    case disunify::variable_deferred: {
                        type_variable* defvar = dis.get_deferred_variable();
                        type_attrvar* v = cxt.ast.new_type_attrvar(defvar, first);
                        defvar->replace_with(v, cxt.unify.unions);
                        cout << "FREEZE ";
                        type_show ts;
                        ts(first);
                        cout << endl;
                        break;
                    }
                    case disunify::attrvar_deferred: {
                        type_attrvar* defatr = dis.get_deferred_attrvar();
                        type_attrvar* v = cxt.ast.new_type_attrvar(defatr->var, first);
                        v->next = defatr;
                        defatr->replace_with(v, cxt.unify.unions);
                        cout << "FREEZE+ ";
                        type_show ts;
                        ts(first);
                        cout << endl;
                        break;
                    }
                }
            }

            return vector<type_struct*> {};
        } else {*/
            while (begin != end) {
                type_clause* clause = *(begin++);
                if (cxt.unify.match_goal_rule(first, clause)) {
                    fresh = cxt.inst.inst_rule(clause->head, clause->cyck, clause->impl, clause->id);
                    cxt.unify.unify_goal_rule(first, fresh);
                    vector<type_attrvar*> const& d = cxt.unify.get_deferred_goals();
                    cout << "deferred goals: " << d.size() << endl;
                    vector<type_struct*> impl;
                    for (auto i : d) {
                        for (type_attrvar* a = i; i != nullptr; i = i->next) {
                            IF_DEBUG(
                                cout << "THAW ";
                                type_show ts;
                                ts(i->goal);
                                cout << endl;
                            );
                            impl.push_back(i->goal);
                        }
                    }
                    impl.insert(impl.end(), fresh->impl.begin(), fresh->impl.end());
                    impl.insert(impl.end(), goal->impl.begin() + 1, goal->impl.end());
                    return cxt.ast.new_type_clause(goal->head, goal->cyck, move(impl), clause->id);
                }
            }

            //return nullptr;
        //}

        switch (builtin) {
            case builtin_duplicate_term: { 
                if (cxt.unify.exp_exp(cxt.inst(first->args[0]), first->args[1])) {
                    fresh = cxt.ast.new_type_clause(first);
                    vector<type_attrvar*> const& d = cxt.unify.get_deferred_goals();
                    vector<type_struct*> impl;
                    cout << "deferred goals: " << d.size() << endl;
                    for (auto i : d) {
                        for (type_attrvar* a = i; i != nullptr; i = i->next) {
                            IF_DEBUG(
                                cout << "THAW ";
                                type_show ts;
                                ts(i->goal);
                                cout << endl;
                            );
                            impl.push_back(i->goal);
                        }
                    }
                    impl.insert(impl.end(), goal->impl.begin() + 1, goal->impl.end());
                    return cxt.ast.new_type_clause(goal->head, goal->cyck, move(impl), 1);
                }
                return nullptr;
            }
            case builtin_dif: {
                disunify dis;

                switch (dis.exp_exp(first->args[0], first->args[1])) {
                    case disunify::same:
                        return nullptr;
                    case disunify::variable_deferred: {
                        type_variable* defvar = dis.get_deferred_variable();
                        type_attrvar* v = cxt.ast.new_type_attrvar(defvar, first);
                        defvar->replace_with(v, cxt.unify.unions);
                        IF_DEBUG(
                            cout << "FREEZE ";
                            type_show ts;
                            ts(first);
                            cout << endl;
                        );
                        break;
                    }
                    case disunify::attrvar_deferred: {
                        type_attrvar* defatr = dis.get_deferred_attrvar();
                        type_attrvar* v = cxt.ast.new_type_attrvar(defatr->var, first);
                        v->next = defatr;
                        defatr->replace_with(v, cxt.unify.unions);
                        IF_DEBUG(
                            cout << "FREEZE+ ";
                            type_show ts;
                            ts(first);
                            cout << endl;
                        );
                        break;
                    }
                    case disunify::different:
                        break;
                }

                fresh = cxt.ast.new_type_clause(first);
                vector<type_struct*> impl(goal->impl.begin() + 1, goal->impl.end());
                return cxt.ast.new_type_clause(goal->head, goal->cyck, move(impl), 1);
            }
            default:
                return nullptr;
        }
    }


    type_clause* reget() {
        //return goal;
        return fresh;
        //return clause;
        //return history;
    }

    bool at_end() {
        return begin == end;
    }
};

vector<type_clause*> const unfolder::invalid {};

//----------------------------------------------------------------------------
// Transitive Closure

class solver {
    static int next_id;
    int const id;

    context cxt;
    int const trail_checkpoint;
    int const env_checkpoint;
    vector<unique_ptr<unfolder>> or_stack;
    int const max_depth;
    int depth;

public:
    solver(const solver&) = delete;
    solver(solver&&) = default;
    solver& operator= (const solver&) = delete;

    solver(atoms &names, env_type &env, type_clause *goal, int d) 
    : id(++next_id)
    , cxt(names, env)
    , trail_checkpoint(cxt.unify.checkpoint())
    , env_checkpoint(cxt.ast.checkpoint())
    , max_depth(d)
    {
        //depth_profile p(max_depth);
        or_stack.emplace_back(new unfolder(cxt, goal, 0));
        //cout << "SOLVER " << id << " CONS\n";
    }

    ~solver() {
        //cout << "SOLVER " << id << " DEST\n";
        stop();
    }

    type_clause *next_goal;

    type_clause* get() {
        depth_profile p(max_depth);
        //cout << "SOLVER GET\n";
        while (!or_stack.empty()) {
            unfolder &src = *(or_stack.back());
            next_goal = src.get();
            //cout << "SOLVER GOT\n";
            if (next_goal != nullptr) {
                //cout << "[" << or_stack.size() << "] ";
                //(type_show {}) (src.goal);
                //cout << "\n";
                //cout << "SUCC\n";
                if (next_goal->impl.empty()) {
                    return next_goal;
                }
                //if (src.at_end()) { // LCO
                //    or_stack.pop_back();
                //    cout << "[" << or_stack.size() << "] LCO\n";
                //}
                //cout << or_stack.size() << " " << next_goal->impl.size() << " <= " << max_depth << endl;
                if (or_stack.size() + next_goal->impl.size() <= max_depth) {
                    //cout << "PUSH" << endl;
                    or_stack.emplace_back(new unfolder(cxt, next_goal, depth));
                } else {
                    cout << "EXCEED\n";
                    or_stack.pop_back(); 
                    cout << "[" << or_stack.size() << "]\n";
                    while (!or_stack.empty() && or_stack.back()->at_end()) {
                        or_stack.pop_back();
                    }
                }
            } else {
                cout << "FAIL\n";
                or_stack.pop_back(); 
                cout << "[" << or_stack.size() << "]\n";
                while (!or_stack.empty() && or_stack.back()->at_end()) {
                    or_stack.pop_back();
                }
            }
        }
        cout << "FINISH\n";
        or_stack.clear();
        cxt.unify.backtrack(trail_checkpoint);
        cxt.ast.backtrack(env_checkpoint);
        return nullptr;
        /*
        next_goal = cxt.ast.new_type_clause(
            cxt.ast.new_type_struct(cxt.names.find("np")->second, vector<type_expression*> {}),
            set<type_variable*> {},
            vector<type_struct*> {}
        );
        return next_goal;
        */
    }

    ostream& show_proof(ostream& out) {
        out << "PROOF:" << endl;
        type_show ts;
        for (auto i = or_stack.begin(); i != or_stack.end(); ++i) {
            type_clause *t = (*i)->reget();
            //if (t->impl.size() > 0) {
                //out << "<" << (*i)->depth << ">";
                //ts(t->head);
                //ts((*i)->reget());
                ts(t);
            //}
            out << "." << endl;
        }
        return out;
    }

    virtual void stop() {
        //cout << "SOLVER " << id << " STOP\n";
        or_stack.clear();
        cxt.unify.backtrack(trail_checkpoint);
        cxt.ast.backtrack(env_checkpoint);
    }

    type_clause* reget() {
        return next_goal;
    }

    virtual bool at_end() {
        return or_stack.empty();
    }
};

int solver::next_id = 0;

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
    int clause_id;

    atoms names = {
        make_pair("np", ast.new_type_atom("np")),
        make_pair("yes", ast.new_type_atom("yes"))
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
        } if (test(is_lower) || test(is_minus)) {
            bool negated = accept(is_minus);
            type_atom* a = atom();
            if (accept(is_brace_open)) {
                vector<type_expression*> terms = parse_terms();
                expect(is_brace_close);
                return ast.new_type_struct(a, move(terms), negated);
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
        bool negated = accept(is_minus);
        type_atom* functor = atom();
        if(accept(is_brace_open)) {
            vector<type_expression*> terms {parse_terms()};
            expect(is_brace_close);
            space();
            return ast.new_type_struct(functor, move(terms), negated);
        } else {
            space();
            return ast.new_type_struct(functor, vector<type_expression*> {}, negated);
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
        return ast.new_type_clause(head, move(cyck), move(impl), ++clause_id);
    }

    explicit term_parser(heap &ast) : ast(ast), clause_id(0) {}

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

        ///*
        cout << endl;
        for (auto const& fun : env) {
            for (auto const& c : fun.second) {
                show_type(c);
                cout << "." << endl;
            }
        }
        cout << endl;
        //*/


        get_variables gv;
        type_clause *answer;
        //int const count = 100;
        int const count = 100;
        context cxt(names, env);
        for (vector<type_struct*> &goal : goals) {
            cout << ":- ";
            for (auto g = goal.cbegin(); g != goal.cend(); g++) {
                show_type(*g);
                if (g + 1 != goal.cend()) {
                    cout << ", ";
                }
            }
            cout << "." << endl << endl;
            //for (int i = 0; i < count; ++i) {
            for (int i = count - 1; i < count; ++i) {
                solver solve(names, env, ast.new_type_clause(ast.new_type_struct(
                    names.find("yes")->second, gv(goal), false), set<type_variable*> {}, goal), i + 1);
                answer = solve.get();
                if (answer != nullptr) {
                    cout << "DEPTH " << depth_profile::report()
                        << " ELAPSED TIME: " << profile::report() << "us\n";
                    cout << endl;
                    solve.show_proof(cout);
                    cout << endl;
                    show_type(answer->head);
                    cout << "." << endl << endl;
                    solve.stop();
                    goto next;
                } else {
                    IF_DEBUG(
                        cout << "DEPTH " << depth_profile::report()
                        << " ELAPSED TIME: " << profile::report() << "us\n";
                    );
                }

                solve.stop();
            }
            //cout << "ELAPSED TIME: " << profile::report() / static_cast<double>(count) << "us\n";
            cout << "NP\n\n";
        next: continue;
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
