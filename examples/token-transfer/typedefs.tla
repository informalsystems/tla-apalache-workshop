-------------------------------- MODULE typedefs ------------------------------
(*
  Type aliases to be used in our specifications:

  @typeAlias: CHAIN = Str;
  @typeAlias: ACCOUNT = Str;
  @typeAlias: ADDR = <<CHAIN, ACCOUNT>>;
  @typeAlias: BANK = (ADDR -> Int);

  @typeAlias: DENOM = Str;
  @typeAlias: DADDR = <<CHAIN, ACCOUNT, DENOM>>;
 *)
typedefs_dummy == FALSE
===============================================================================
