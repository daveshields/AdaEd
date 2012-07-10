generic
    MAX_TEXT_LENGTH: POSITIVE;
package GEN_TEXT_HANDLER is
    subtype TEXT_LENGTH is NATURAL range 0..MAX_TEXT_LENGTH;
    type TEXT(LENGTH: TEXT_LENGTH := 0) is private;
private
    type TEXT(LENGTH: TEXT_LENGTH := 0) is
        record
            IMAGE: STRING(1..LENGTH);
        end record;
end GEN_TEXT_HANDLER;

package body GEN_TEXT_HANDLER is
end GEN_TEXT_HANDLER;

with GEN_TEXT_HANDLER;
package TOKEN_TEXT is
    MAX_TOKEN_LENGTH: constant := 512;
    package TEXT_HANDLER is new GEN_TEXT_HANDLER(MAX_TOKEN_LENGTH);
end TOKEN_TEXT;

with TOKEN_TEXT; use TOKEN_TEXT;
procedure MAIN is
  use TEXT_HANDLER;
  TOKEN : TEXT;
begin -- MAIN
 null;
end MAIN;

