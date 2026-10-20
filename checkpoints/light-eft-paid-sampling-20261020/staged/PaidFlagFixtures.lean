import LightEFTPaidSamplingStage.PaidFlagSampleComposition

namespace LightEFTSpanners.PaidFlagFixtures

example : PaidFlagSerialization.execute ([] : List Nat) [] = some [] := rfl
example : PaidFlagSerialization.execute [7,7,9] [true,false,true] =
    some [(7,true),(7,false),(9,true)] := rfl
example : PaidFlagSerialization.execute [7] [] = none := rfl
example : PaidFlagSerialization.execute ([] : List Nat) [true] = none := rfl
example : PaidFlagSampleComposition.execute [] [] = some [] := rfl
example : PaidFlagSampleComposition.execute [(0,1),(0,1),(2,2)] [true,false,true] =
    some [(0,1),(2,2)] := rfl
example : PaidFlagSampleComposition.execute [(1,0),(1,0)] [true,true] =
    some [(1,0),(1,0)] := rfl
example : PaidFlagSampleComposition.execute [(0,0),(2,1)] [false,false] = some [] := rfl

end LightEFTSpanners.PaidFlagFixtures
