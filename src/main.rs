// mod expr;
// mod infer;

use std::collections::{HashMap, HashSet};

type Name = String;

pub enum Expr {
    Int(u64),
    Var(Name),
    Fun(Vec<String>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Let(Name, Box<Expr>, Box<Expr>),
}

type Id = usize;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Const(Name),
    Arrow(Vec<Type>, Box<Type>),
    Var(Id),
}

#[derive(Clone)]
struct VarEnv {
    vars: HashMap<Name, Type>,
}

impl VarEnv {
    fn new() -> VarEnv {
        VarEnv {
            vars: HashMap::new(),
        }
    }

    fn add(&mut self, name: &String, ty: Type) {
        self.vars.insert(name.clone(), ty);
    }

    fn get(&self, name: &String) -> Type {
        match self.vars.get(name) {
            Option::Some(ty) => ty.clone(),
            Option::None => panic!("var type doesn't exist"),
        }
    }
}

struct TypeVarEnv {
    next: Id,
    substs: HashMap<Id, Type>,
    generics: HashSet<Id>,
}

impl TypeVarEnv {
    fn new() -> TypeVarEnv {
        TypeVarEnv {
            next: 0,
            substs: HashMap::new(),
            generics: HashSet::new(),
        }
    }

    fn next(&mut self) -> Id {
        let id = self.next;
        self.next += 1;
        id
    }

    fn next_var(&mut self) -> Type {
        let id = self.next();
        Type::Var(id)
    }

    fn get(&self, id: &Id) -> Type {
        match self.substs.get(id) {
            None => Type::Var(id.clone()),
            Some(Type::Var(other_id)) => self.get(other_id),
            Some(ty) => ty.clone(),
        }
    }

    fn has_subst(&self, id: &Id) -> Option<Type> {
        match self.substs.get(id) {
            None => None,
            Some(ty) => Some(ty.clone()),
        }
    }

    fn add_subst(&mut self, id: &Id, ty: Type) {
        match self.substs.insert(id.clone(), ty) {
            None => (),
            _ => {
                panic!("subst already existed")
            }
        }
    }
}

fn unify(env: &mut TypeVarEnv, ty1: &Type, ty2: &Type) {
    match (ty1, ty2) {
        (Type::Const(name1), Type::Const(name2)) if name1 == name2 => (),
        (Type::Arrow(param_tys1, ret_ty1), Type::Arrow(param_tys2, ret_ty2)) => {
            for (param_ty1, param_ty2) in param_tys1.iter().zip(param_tys2) {
                unify(env, param_ty1, param_ty2)
            }
            unify(env, &ret_ty1, &&ret_ty2);
        }
        (Type::Var(id1), Type::Var(id2)) if id1 == id2 => panic!("unifying the same type variable"),
        (Type::Var(id1), Type::Var(id2)) => match (env.has_subst(id1), env.has_subst(id2)) {
            (Some(ty1), Some(ty2)) => unify(env, &ty1, &ty2),
            (Some(ty1), None) => unify(env, &ty1, ty2),
            (None, Some(ty2)) => unify(env, ty1, &ty2),
            (None, None) => {
                // Bias linking id2 to id1
                // TODO: occurs_check_adjust_levels
                env.add_subst(id2, ty1.clone())
            }
        },
        (Type::Var(id), _) => env.add_subst(id, ty2.clone()),
        (_, Type::Var(id)) => env.add_subst(id, ty1.clone()),
        (_, _) => panic!("cannot unify types"),
    }
}

fn generalize(env: &mut TypeVarEnv, ty: &Type) -> Type {
    match ty {
        Type::Var(_) => {
            let id = env.next();
            Type::Var(id)
        }
        Type::Const(name) => Type::Const(name.clone()),
        Type::Arrow(params, ret) => {
            let params = params
                .into_iter()
                .map(|param| generalize(env, param))
                .collect::<Vec<Type>>();
            let ret = Box::new(generalize(env, ret));
            Type::Arrow(params, ret)
        }
    }
}

// TODO: ty should be & ?
fn instantiate(env: &mut TypeVarEnv, ty: Type) -> Type {
    fn f(env: &mut TypeVarEnv, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => match env.has_subst(id) {
                None => {
                    let id = env.next();
                    Type::Var(id)
                }
                Some(ty) => f(env, &ty),
            },
            Type::Arrow(params, ret) => {
                let params = params
                    .into_iter()
                    .map(|param| f(env, param))
                    .collect::<Vec<Type>>();
                let ret = Box::new(f(env, ret));
                Type::Arrow(params, ret)
            }
            Type::Const(name) => Type::Const(name.clone()),
        }
    }
    f(env, &ty)
}

fn match_fun_ty(type_var_env: &mut TypeVarEnv, num_params: usize, ty: &Type) -> (Vec<Type>, Type) {
    fn f(
        first: bool,
        type_var_env: &mut TypeVarEnv,
        num_params: usize,
        ty: &Type,
    ) -> (Vec<Type>, Type) {
        match (first, ty) {
            (_, Type::Arrow(param_tys, ret_ty)) => {
                if param_tys.len() != num_params {
                    panic!("unexpected number of arguments");
                }
                (param_tys.clone(), *ret_ty.clone())
            }
            (true, Type::Var(id)) => {
                let ty = type_var_env.get(id);
                f(false, type_var_env, num_params, &ty)
            }
            (false, Type::Var(id)) => {
                let param_tys = (0..num_params)
                    .map(|_| type_var_env.next_var())
                    .collect::<Vec<Type>>();
                let ret_ty = type_var_env.next_var();
                let ty = Type::Arrow(param_tys.clone(), Box::new(ret_ty.clone()));
                type_var_env.add_subst(id, ty);
                (param_tys, ret_ty)
            }
            _ => {
                panic!("expecte a function")
            }
        }
    }
    f(true, type_var_env, num_params, ty)
}

fn infer_with_env(var_env: &mut VarEnv, type_var_env: &mut TypeVarEnv, expr: &Expr) -> Type {
    match expr {
        Expr::Int(_) => Type::Const(String::from("int")),
        Expr::Var(name) => {
            let ty = var_env.get(name);
            println!("ty = {:?}", ty);
            instantiate(type_var_env, ty)
        }
        Expr::Fun(params, body) => {
            let param_tys = params
                .into_iter()
                .map(|_| type_var_env.next_var())
                .collect::<Vec<Type>>();
            let mut fn_var_env = var_env.clone();
            for (name, ty) in params.iter().zip(&param_tys) {
                fn_var_env.add(name, ty.clone())
            }
            let body = infer_with_env(&mut fn_var_env, type_var_env, body);
            Type::Arrow(param_tys, Box::new(body))
        }
        Expr::Let(name, value, body) => {
            let value_ty = infer_with_env(var_env, type_var_env, value);
            let generalized_ty = generalize(type_var_env, &value_ty);
            var_env.add(name, generalized_ty);
            infer_with_env(var_env, type_var_env, body)
        }
        Expr::Call(fn_expr, args) => {
            let fn_ty = infer_with_env(var_env, type_var_env, fn_expr);
            let (param_tys, ret_ty) = match_fun_ty(type_var_env, args.len(), &fn_ty);
            for (param_ty, arg) in param_tys.iter().zip(args) {
                let arg_ty = infer_with_env(var_env, type_var_env, arg);
                unify(type_var_env, param_ty, &arg_ty)
            }
            ret_ty
        }
    }
}

fn infer(expr: &Expr) -> Type {
    let mut var_env = VarEnv::new();
    let mut type_var_env = TypeVarEnv::new();
    infer_with_env(&mut var_env, &mut type_var_env, expr)
}

#[test]
fn test_infer() {
    fn const_t(name: &str) -> Type {
        Type::Const(String::from(name))
    }
    fn var_e(name: &str) -> Expr {
        Expr::Var(String::from(name))
    }
    // assert_eq!(infer(&Expr::Int(1)), const_t("int"));
    // assert_eq!(
    //     infer(&Expr::Let(
    //         String::from("a"),
    //         Box::new(Expr::Int(1)),
    //         Box::new(Expr::Var(String::from("a")))
    //     )),
    //     const_t("int")
    // );
    assert_eq!(
        infer(&Expr::Fun(vec![String::from("x")], Box::new(var_e("x")))),
        Type::Arrow(vec![Type::Var(0)], Box::new(Type::Var(0)))
    )
}

fn main() {
    println!("Hello, world!");
}
