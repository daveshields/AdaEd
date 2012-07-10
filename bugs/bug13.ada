PROCEDURE Tax IS
  SUBTYPE NonNegFloat IS Float RANGE 0.0 .. Float'Last;
  Tot_Tax        : NonNegFloat;
  Taxable_Income : Float;
BEGIN
  Float (Tot_Tax) := Taxable_Income;
END TAX;
