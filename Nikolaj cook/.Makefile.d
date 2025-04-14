bisimulation.vo bisimulation.glob bisimulation.v.beautified bisimulation.required_vo: bisimulation.v pi.vo encoding.vo
bisimulation.vos bisimulation.vok bisimulation.required_vos: bisimulation.v pi.vos encoding.vos
cbpv.vo cbpv.glob cbpv.v.beautified cbpv.required_vo: cbpv.v 
cbpv.vos cbpv.vok cbpv.required_vos: cbpv.v 
early_semantics_de_bruijn.vo early_semantics_de_bruijn.glob early_semantics_de_bruijn.v.beautified early_semantics_de_bruijn.required_vo: early_semantics_de_bruijn.v 
early_semantics_de_bruijn.vos early_semantics_de_bruijn.vok early_semantics_de_bruijn.required_vos: early_semantics_de_bruijn.v 
encoding.vo encoding.glob encoding.v.beautified encoding.required_vo: encoding.v cbpv.vo pi.vo
encoding.vos encoding.vok encoding.required_vos: encoding.v cbpv.vos pi.vos
late_semantics_de_bruijn.vo late_semantics_de_bruijn.glob late_semantics_de_bruijn.v.beautified late_semantics_de_bruijn.required_vo: late_semantics_de_bruijn.v 
late_semantics_de_bruijn.vos late_semantics_de_bruijn.vok late_semantics_de_bruijn.required_vos: late_semantics_de_bruijn.v 
op_correspond.vo op_correspond.glob op_correspond.v.beautified op_correspond.required_vo: op_correspond.v pi.vo cbpv.vo encoding.vo bisimulation.vo
op_correspond.vos op_correspond.vok op_correspond.required_vos: op_correspond.v pi.vos cbpv.vos encoding.vos bisimulation.vos
pi.vo pi.glob pi.v.beautified pi.required_vo: pi.v 
pi.vos pi.vok pi.required_vos: pi.v 
