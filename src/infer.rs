use crate::expr::{Expr, Id, Level, Name, Type};
use std::collections::HashMap;

// struct IdEnv {
//     count: Id,
// }

// impl IdEnv {
//     fn next_id(&mut self) -> Id {
//         let i = self.count;
//         self.count = self.count + 1;
//         i
//     }

//     fn new_var(&mut self, level: Level) -> Type {
//         Type::Var(TypeVar::Unbound(self.next_id(), level))
//     }

//     fn new_gen_var(&mut self) -> Type {
//         Type::Var(TypeVar::Generic(self.next_id()))
//     }
// }

// fn occurs_check_adjust_levels(tvar_id: &Id, tvar_level: &Level, ty: &mut Type) {
//     fn f(tvar_id: &Id, tvar_level: &Level, ty: &mut Type) {
//         match ty {
//             Type::Var(TypeVar::Link(ty)) => f(tvar_id, tvar_level, ty),
//             Type::Var(TypeVar::Generic(_)) => panic!("unexpected"),
//             Type::Var(TypeVar::Unbound(ref other_id, ref other_level)) => {
//                 if other_id == tvar_id {
//                     panic!("recursive types")
//                 } else {
//                     if *other_level > *tvar_level {
//                         *ty = Type::Var(TypeVar::Unbound(*other_id, *tvar_level))
//                     }
//                 }
//             }
//             Type::App(ty, args) => {
//                 f(tvar_id, tvar_level, ty);
//                 for arg in args.into_iter() {
//                     f(tvar_id, tvar_level, arg);
//                 }
//             }
//             Type::Arrow(params, ret) => {
//                 for param in params.into_iter() {
//                     f(tvar_id, tvar_level, param);
//                 }
//                 f(tvar_id, tvar_level, ret);
//             }
//             Type::Const(_) => (),
//         }
//     }
//     f(tvar_id, tvar_level, ty)
// }

// fn unify(ty1: &mut Type, ty2: &mut Type) {
//     if ty1 == ty2 {
//         return ();
//     }
//     match (ty1, ty2) {
//         (Type::Const(name1), Type::Const(name2)) if name1 == name2 => (),
//         (Type::App(ty1, args1), Type::App(ty2, args2)) => {
//             if args1.len() != args2.len() {
//                 panic!("unify app wrong len");
//             }
//             unify(ty1, ty2);
//             let zipped = args1.into_iter().zip(args2.into_iter());
//             for (arg1, arg2) in zipped {
//                 unify(arg1, arg2);
//             }
//         }
//         (Type::Arrow(params1, ret1), Type::Arrow(params2, ret2)) => {
//             let zipped = params1.into_iter().zip(params2.into_iter());
//             for (param1, param2) in zipped {
//                 unify(param1, param2);
//             }
//             unify(ret1, ret2);
//         }
//         (Type::Var(TypeVar::Link(ty1)), _) => unify(ty1, ty2),
//         (_, Type::Var(TypeVar::Link(ty2))) => unify(ty1, ty2),
//         (Type::Var(TypeVar::Unbound(id1, _)), Type::Var(TypeVar::Unbound(id2, _)))
//             if id1 == id2 =>
//         {
//             panic!("unify unbound the same");
//         }
//         (Type::Var(TypeVar::Unbound(ref id, ref level)), ty) => {
//             occurs_check_adjust_levels(id, level, ty);
//             *ty1 = Type::Var(TypeVar::Link(Rc::new(ty)))
//         }
//         (ty, Type::Var(TypeVar::Unbound(ref id, ref level))) => {
//             occurs_check_adjust_levels(id, level, ty);
//             *ty2 = Type::Var(TypeVar::Link(Rc::new(ty)))
//         }
//         (_, _) => {
//             panic!("unify cannot");
//         }
//     }
// }

// fn generalize(level: &Level, ty: &Type) -> Type {
//     match ty {
//         Type::Var(TypeVar::Unbound(id, other_level)) if other_level > level => {
//             Type::Var(TypeVar::Generic(id.clone()))
//         }
//         Type::App(ty, args) => {
//             let ty = generalize(level, ty);
//             let args = args.into_iter().map(|arg| generalize(level, arg)).collect();
//             Type::App(Box::new(ty), args)
//         }
//         Type::Arrow(params, ret) => {
//             let params = params
//                 .into_iter()
//                 .map(|param| generalize(level, param))
//                 .collect();
//             let ret = generalize(level, ret);
//             Type::Arrow(params, Box::new(ret))
//         }
//         Type::Var(TypeVar::Link(ty)) => generalize(level, ty),
//         Type::Var(_) | Type::Const(_) => *ty,
//     }
// }

// struct IdVarEnv {
//     id_vars: HashMap<Id, Type>,
// }

// fn instantiate(level: &Level, ty: &Type) -> Type {
//     let mut name_env = NameEnv {
//         count: 0,
//         names: HashMap::new(),
//     };
// }

struct InferEnv {
    types: Vec<Type>,
    vars: HashMap<Name, Id>,
}

impl InferEnv {
    fn new() -> InferEnv {
        InferEnv {
            types: vec![],
            vars: HashMap::new(),
        }
    }

    fn get_var(&self, name: &String) -> &Type {
        match self.vars.get(name) {
            Option::Some(id) => match self.types.get(id.clone()) {
                Option::Some(ty) => ty.clone(),
                Option::None => panic!("id not in types"),
            },
            Option::None => panic!("var type doesn't exist"),
        }
    }
}

fn instantiate(ty: &Type) -> Type {
    // let mut id_var_map = HashMap::new();
    fn f(ty: &Type) -> Type {
        match ty {
            Type::Const(name) => Type::Const(name.clone()),
            _ => panic!("TODO"),
        }
    }
    f(ty)
}

fn infer(env: &mut InferEnv, expr: &Expr) -> Type {
    match expr {
        Expr::Int(_) => Type::Const(String::from("int")),
        Expr::Var(name) => {
            let ty = env.get_var(name);
            instantiate(ty)
        }
        Expr::Let(name, value, body) => {}
        _ => panic!("TODO"),
    }
}

#[test]
fn test_infer() {}
