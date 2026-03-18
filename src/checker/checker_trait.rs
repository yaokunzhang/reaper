use crate::analysis::mir_visitor::body_visitor::BodyVisitor;
use crate::analysis::numerical::apron_domain::{
    ApronAbstractDomain, ApronDomainType, GetManagerTrait,
};

pub trait CheckerTrait<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    fn new(body_visitor: &'b mut BodyVisitor<'tcx, 'a, 'compiler, DomainType>) -> Self;

    fn run(&mut self);
}
