use std::marker::PhantomData;

use halo2_proofs::{
    plonk::*,
    circuit::*, arithmetic::FieldExt, poly::Rotation,
};

#[derive(Debug,Clone)]
struct RangeCheckConfig<F: FieldExt,const RANGE:usize> { 
    value: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>
}

impl<F:FieldExt,const RANGE:usize> RangeCheckConfig<F,RANGE> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>
    ) -> Self {
        let q_range_check = meta.selector();

        let config = Self{ q_range_check,value,_marker:PhantomData};

        // Range-check gate, check that value v in range R v < R
        // v * (1 - v) * (2 - v) * .......... * (R-1-v) == 0
        meta.create_gate("Range check", |meta|{
            let q_range_check = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());

            let range_check = |range:usize, value:Expression<F>| {
                (0..range).fold(value.clone(), |expr,i|{
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone() ) 
                })
            };

            Constraints::with_selector(q_range_check,[("range check", range_check(RANGE,value.clone()))])

        });

        config
    }

    fn assign(
        &self,
        mut layouter:impl Layouter<F>,
        value: Value<Assigned<F>>
    ) -> Result<(),Error> {
        layouter.assign_region(|| "Assign value", |mut region| {
            let offset = 0;
            self.q_range_check.enable(&mut region, offset)?;

            region.assign_advice(|| "assign value", self.value, offset, || value)?;

            Ok(())
        })
    }
}

