type 'cfg_type node = Block of 'cfg_type list [@@deriving show];;

module MapInt = Map.Make(Int);;
module MapString = Map.Make(String);;