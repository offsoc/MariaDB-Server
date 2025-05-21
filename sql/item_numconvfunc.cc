/*
   Copyright (c) 2009, 2025, MariaDB Corporation.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1335  USA
*/

#include "mariadb.h"
#include "sql_priv.h"
#include "sql_class.h"
#include "sql_base.h"
#include "m_ctype.h"
#include "strfunc.h"
#include "item_numconvfunc.h"
#include "lex_ident_sys.h"
#include "simple_tokenizer.h"
#include "sql_list.h"
#include "sql_string.h"

#define LIST_CONTAINERS_PROVIDE_EMPTY
#include "simple_parser.h"
#undef LIST_CONTAINERS_PROVIDE_EMPTY


class Format_tokenizer: public Extended_string_tokenizer
{
public:
  Format_tokenizer(CHARSET_INFO *cs, const LEX_CSTRING &str)
   :Extended_string_tokenizer(cs, str)
  { }

  static constexpr uchar _C= 'C'; // Positional currency (C, L, U)
  static constexpr uchar _B= 'B'; // Currency prefix/inline flags ($, B)
  static uchar single_char_token(uchar ch)
  {
    // Single char tokens: $ B . D , G 09 C L U
    static const uchar single_char_token_array[256]=
    {
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0,_B, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, /*  !"#$%&'()*+,-./ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* 0123456789:;<=>? */
       0, 0,_B,_C, 1, 0, 0, 1, 0, 0, 0, 0,_C, 0, 0, 0, /* @ABCDEFGHIJKLMNO */
       0, 0, 0, 1, 0,_C, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* PQRSTUVWXYZ[\]^_ */
       0, 0,_B,_C, 1, 0, 0, 1, 0, 0, 0, 0,_C, 0, 0, 0, /* `abcdefghijklmno */
       0, 0, 0, 1, 0,_C, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* pqrstuvwxyz{|}~. */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, /* ................ */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0  /* ................ */
    };
    return single_char_token_array[ch];
  }
  static bool is_positional_currency(uchar ch)
  {
    return single_char_token(ch) == _C;
  };
  static bool is_currency_flag(uchar ch)
  {
    return single_char_token(ch) == _B;
  }

  enum class TokenID
  {
    // Special purpose tokens:
    tNULL=  0, // returned if the tokenizer failed to detect a token
               // also used if the parser failed to parse a token
    tEMPTY= 1, // returned on empty optional constructs in a grammar like:
               //   rule ::= [ rule1 ]
               // when rule1 does not present in the input.
    tEOF=   2, // returned when the end of input is reached

    // One character tokens
    tCOMMA= ',',
    tDOLLAR= '$',
    tPERIOD= '.',
    tB= 'B',
    tC= 'C',
    tD= 'D',
    tG= 'G',
    tL= 'L',
    tU= 'U',
    tV= 'V',
    tS= 'S',
    // Other tokens, values must be greater than any of the above
    tMI= 256,
    tFM,
    tPR,
    tTM,
    tTM9,
    tTME,
    tZEROS,
    tNINES,
    tXCHAIN,
    tEEEE
  };

  // A helper wrapper for Lex_cstring with convenience methods
  class LS: public Lex_cstring
  {
  public:
    using Lex_cstring::Lex_cstring;
    const char *ptr() const { return str; }
    size_t length() const { return Lex_cstring::length; }
    const char *end() const
    {
      return str ? str + Lex_cstring::length : nullptr;
    }
    static LS empty()
    {
      return empty_clex_str;
    }
    void print(String *str) const
    {
      str->append(ptr(), length());
    }
    LS to_LS() const
    {
      return LS(*this);
    }
    LS ltrim(CHARSET_INFO *cs) const
    {
      const char *start= ptr() + cs->scan(ptr(), end(), MY_SEQ_SPACES);
      return LS(start, end());
    }
    LS ltrim_currency_flags() const
    {
      const char *p= ptr();
      for (p= ptr() ; p < end() && is_currency_flag((uchar) *p) ; p++)
      { }
      return LS(p, end());
    }
  };


  class Token: public LS
  {
  protected:
    TokenID m_id;
  public:
    Token()
     :LS(), m_id(TokenID::tNULL)
    { }
    Token(const LEX_CSTRING &str, TokenID id)
     :LS(str), m_id(id)
    { }
    TokenID id() const { return m_id; }
    static Token empty(const char *pos)
    {
      return Token(Lex_cstring(pos, pos), TokenID::tEMPTY);
    }
    static Token empty()
    {
      return Token(LS::empty(), TokenID::tEMPTY);
    }
    operator bool() const
    {
      return m_id != TokenID::tNULL;
    }
  };


protected:

  Token get_token(CHARSET_INFO *cs)
  {
    if (eof())
      return Token(Lex_cstring(m_ptr, m_ptr), TokenID::tEOF);

    const char *head= m_ptr;

    if (single_char_token((uchar) *head))
    {
      TokenID id= (TokenID) my_toupper(system_charset_info, head[0]);
      return m_ptr++, Token(Lex_cstring(m_ptr - 1, 1), id);
    }
    // Digit chains - return as a single token
    if (head[0] == '0' || head[0] == '9' || head[0] == 'X' || head[0] == 'x')
    {
      for ( ; !get_char(head[0]) ;)
      { }
      if (head[0] == '0')
        return Token(Lex_cstring(head, m_ptr), TokenID::tZEROS);
      if (head[0] == '9')
        return Token(Lex_cstring(head, m_ptr), TokenID::tNINES);
      if (head[0] == 'X' || head[0] == 'x')
        return Token(Lex_cstring(head, m_ptr), TokenID::tXCHAIN);
    }

    // Two-char tokens
    if (m_ptr + 2 <= m_end)
    {
      const LEX_CSTRING str= Lex_cstring(m_ptr, 2);
      if ("MI"_Lex_ident_column.streq(str))
        return m_ptr+=2, Token(str, TokenID::tMI);
      if ("FM"_Lex_ident_column.streq(str))
        return m_ptr+=2, Token(str, TokenID::tFM);
      if ("PR"_Lex_ident_column.streq(str))
        return m_ptr+=2, Token(str, TokenID::tPR);
      if ("TM"_Lex_ident_column.streq(str))
      {
        if (m_ptr + 3 <= m_end)
        {
          // Three-char tokens: TM9 TME
          if (m_ptr[2] == '9')
            return m_ptr+= 3, Token(Lex_cstring(head, m_ptr), TokenID::tTM9);
          if (m_ptr[2]=='E' || m_ptr[2]=='e')
            return m_ptr+= 3, Token(Lex_cstring(head, m_ptr), TokenID::tTME);
        }
        return m_ptr+=2, Token(Lex_cstring(head, m_ptr), TokenID::tTM);
      }
    }

    // Four-char tokes: EEEE
    if (m_ptr + 4 <= m_end)
    {
      const LEX_CSTRING str= Lex_cstring(m_ptr, 4);
      if ("EEEE"_Lex_ident_column.streq(str))
        return m_ptr+=4, Token(str, TokenID::tEEEE);
    }

    return Token(Lex_cstring(m_ptr, m_ptr), TokenID::tNULL);
  }

#ifndef DBUG_OFF
  // A helper method for debugging
  void trace_tokens(CHARSET_INFO *cs, const LEX_CSTRING &fmt)
  {
    Format_tokenizer::Token tok;
    for (tok= get_token(cs) ;
         tok && tok.id() != Format_tokenizer::TokenID::tEOF;
         tok= get_token(cs))
    { }
  }
#endif

}; // End of class Format_tokenizer


/*
   A convenience operator,
   to use:       "123"_LS
   instead of:   CSTRING_WITH_LEN("123").
   Must be outside of a class.
*/
static inline constexpr
Format_tokenizer::LS
operator""_LS(const char *str, size_t length)
{
  return Format_tokenizer::LS(str, length);
}



class Format_parser: public Format_tokenizer,
                     public Parser_templates
{
private:
  THD *m_thd;
  Token m_look_ahead_token;
  LEX_CSTRING m_func_name;
  const char *m_start;
  bool m_error; // Syntax or raised by the caller, e.g. in methods add()

  using Parser= Format_parser; // for a shorter notation inside the class

public:

  Format_parser()
   :Format_tokenizer(&my_charset_bin, null_clex_str),
    m_thd(nullptr),
    m_look_ahead_token(Token()),
    m_func_name(null_clex_str),
    m_start(nullptr),
    m_error(true)
  { }

  Format_parser(THD *thd, const LEX_CSTRING func_name,
                CHARSET_INFO *cs, const LEX_CSTRING &str)
   :Format_tokenizer(cs, str),
    m_thd(thd),
    m_look_ahead_token(get_token(cs)),
    m_func_name(func_name),
    m_start(str.str),
    m_error(false)
  { }
  bool set_syntax_error()
  {
    m_error= true;
    return false;
  }
  bool set_fatal_error()
  {
    m_error= true;
    return false;
  }

  bool is_error() const
  {
    return m_error;
  }

  LS buffer() const
  {
    return LS(m_start, m_end);
  }

  TokenID look_ahead_token_id() const
  {
    return is_error() ? TokenID::tNULL : m_look_ahead_token.id();
  }
  /*
    Return an empty token at the position of the current
    look ahead token with a zero length. Used for optional grammar constructs.

    For example, if the grammar is "rule ::= ruleA [ruleB] ruleC"
    and the input is "A C", then:
    - the optional rule "ruleB" will point to the input position "C"
      with a zero length
    - while the rule "ruleC" will point to the same input position "C"
      with a non-zero length
  */
  Token empty_token() const // For templates in simple_parser.h
  {
    return Token::empty(m_look_ahead_token.str);
  }
  static Token null_token() // For templates in simple_parser.h
  {
    return Token();
  }

  /*
    Return the current look ahead token and scan the next one
  */
  Token shift()
  {
    DBUG_ASSERT(!is_error());
    const Token res= m_look_ahead_token;
    m_look_ahead_token= get_token(m_cs);
    return res;
  }

public:

  /*
    Return the current look ahead token if it matches the given ID
    and scan the next one.
  */
  Token token(TokenID id)
  {
    if (m_look_ahead_token.id() != id || is_error())
      return null_token();
    return shift();
  }

  void parse_error_at(THD *thd,
                      Sql_state_errno_level::enum_warning_level level,
                      const char *pos= nullptr) const
  {
    const LS buf= buffer();
    const char *bufend= buf.end();
    if (!pos)
      pos= m_look_ahead_token.str;
    DBUG_ASSERT(pos >= buf.str && pos <= bufend);
    ErrConvString txt(pos, bufend - pos, thd->variables.character_set_client);
    if (level == Sql_state_errno_level::WARN_LEVEL_ERROR)
      my_error(ER_WRONG_VALUE_FOR_TYPE, MYF(0),
               "<number format>", txt.ptr(), m_func_name.str);
    else
      push_warning_printf(thd, level,
                          ER_WRONG_VALUE_FOR_TYPE,
                          ER_THD(thd, ER_WRONG_VALUE_FOR_TYPE),
                          "<number format>", txt.ptr(), m_func_name.str);
  }

  enum feature_t
  {
    F_NONE=                 0,
    F_INT_DIGIT=       1 << 0,
    F_INT_B=           1 << 1,
    F_INT_DOLLAR=      1 << 2,
    F_INT_GROUP_COMMA= 1 << 3,
    F_INT_GROUP_G=     1 << 4,
    F_INT_HEX=         1 << 5,

    F_FRAC_DIGIT=      1 << 10,
    F_FRAC_B=          1 << 11,
    F_FRAC_DOLLAR=     1 << 12,
    F_FRAC_DEC_PERIOD= 1 << 13,
    F_FRAC_DEC_D=      1 << 14,
    F_FRAC_DEC_V=      1 << 15,
    F_FRAC_DEC_CLU=    1 << 16,

    F_EEEE=            1 << 17,

    F_POST_CLU=        1 << 20,
    F_PREF_CLU=        1 << 21,
    F_PREF_B=          1 << 22,
    F_PREF_DOLLAR=     1 << 23,

    F_PREF_SIGN=       1 << 25,
    F_POST_SIGN=       1 << 26,
    F_FMT_TM=          1 << 27,
    F_FMT_FLAG_FM=     1 << 28
  };

//private:


  // A common parent class for various containers
  class LS_container: public LS
  {
  public:
    using LS::LS;
    static LS_container empty(const Parser &parser)
    {
      return parser.empty_token();
    }
    static LS_container empty()
    {
      return LS::empty();
    }
    operator bool() const
    {
      return Lex_cstring::str != nullptr;
    }
    /*
      Contatenate list elements into a single container.
      There must be no any delimiters in between.
      As far as spaces are not allowed in the format, it's always true.
    */
    bool concat(const Lex_cstring && rhs)
    {
      if (!ptr())
      {
        Lex_cstring::operator=(std::move(rhs));
        return false;
      }
      if (rhs.length == 0)
        return false;
      if (end() != rhs.str)
      {
        DBUG_ASSERT(0);
        return true;
      }
      Lex_cstring::length+= rhs.length;
      return false;
    }
    // Methods that allow to pass it as a container to LIST.
    size_t count() const { return length(); }
    bool add(Parser *p, const Lex_cstring && rhs)
    {
      return concat(std::move(rhs));
    }
  };


  /*
    Counters for flags '$' and 'B' and group separators '.' and 'G'.

    Currency prefix flags can have flags '$' and 'B':           'BC99.9'

    Integer and fraction parts of the format can have
    digits '0', '9', 'X', and additional elements:
    - Integer digits can have both flags and group separators:  '9,B,9$'
    - Fractional digits can have flags '$' and 'B' only:        '.9B$9'
      (but cannot have group separators)
  */
  class Decimal_flag_counters
  {
  public:
    size_t m_dollar_count;
    size_t m_B_count;
    size_t m_comma_count;
    size_t m_G_count;
    Decimal_flag_counters()
     :m_dollar_count(0),
      m_B_count(0),
      m_comma_count(0),
      m_G_count(0)
    { }
    Decimal_flag_counters(Decimal_flag_counters && rhs)
     :m_dollar_count(rhs.m_dollar_count),
      m_B_count(rhs.m_B_count),
      m_comma_count(rhs.m_comma_count),
      m_G_count(rhs.m_G_count)
    { }
    Decimal_flag_counters & operator=(Decimal_flag_counters && rhs)
    {
      m_dollar_count= rhs.m_dollar_count;
      m_B_count= rhs.m_B_count;
      m_comma_count= rhs.m_comma_count;
      m_G_count= rhs.m_G_count;
      return *this;
    }
    void join(Decimal_flag_counters && rhs)
    {
      m_dollar_count+= rhs.m_dollar_count;
      m_B_count+= rhs.m_B_count;
      m_comma_count+= rhs.m_comma_count;
      m_G_count+= rhs.m_G_count;
    }
    void add(char ch)
    {
      if (ch == '$')
        m_dollar_count++;
      if (ch == 'B')
        m_B_count++;
      if (ch == ',')
        m_comma_count++;
      if (ch == 'G')
        m_G_count++;
    }
    // Methods needed to pass this class to templates in simple_parser.h
    static Decimal_flag_counters empty(const Parser & parser)
    {
      return Decimal_flag_counters();
    }
    static Decimal_flag_counters empty()
    {
      return Decimal_flag_counters();
    }
    operator bool() const
    {
      return true;
    }
    // Other methods
    size_t flag_length() const
    {
      return m_dollar_count + m_B_count + m_comma_count + m_G_count;
    }
  };


  /********** Rules consisting of a single token *****/

  class TokenEOF: public TOKEN<Parser, TokenID::tEOF> { using TOKEN::TOKEN; };

  // Inline flag 'B'
  class TokenB: public TOKEN<Parser, TokenID::tB> { using TOKEN::TOKEN; };

  /*
    The following chains are returned by the tokenizer as a single token:

      zeros: '0' [ '0'... ]
      nines: '9' [ '9'... ]
      xchain: 'X' [ 'X'...]
  */
  class Zeros: public TOKEN<Parser, TokenID::tZEROS>   { using TOKEN::TOKEN; };
  class Nines: public TOKEN<Parser, TokenID::tNINES>   { using TOKEN::TOKEN; };
  class XChain: public TOKEN<Parser, TokenID::tXCHAIN> { using TOKEN::TOKEN; };


  /********** Rules consisting of a single token with their own container ***/

  /*** The containers appear in the final structure Foram::Goal after parsing */

  // Format prefix flag 'FM'. There are no any other format prefix flags.
  class Format_flags: public LS_container
  {
  public:
    using LS_container::LS_container;
    using Container= CONTAINER1<Parser, Format_flags>;
    using LParser= TOKEN<Parser, TokenID::tFM>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT("FM"_Lex_ident_column.streq(to_LS()));
      return F_FMT_FLAG_FM;
    }
  };

  // EEEE - scientific modifier
  class EEEE: public LS_container
  {
  public:
    using LS_container::LS_container;
    using Container= CONTAINER1<Parser, EEEE>;
    using LParser= TOKEN<Parser, TokenID::tEEEE>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT("EEEE"_Lex_ident_column.streq(to_LS()));
      return F_EEEE;
    }
  };

  // prefix_sign: 'S'
  class Prefix_sign: public LS_container
  {
  public:
    using LS_container::LS_container;
    using Container= CONTAINER1<Parser, Prefix_sign>;
    using LParser= TOKEN<Parser, TokenID::tS>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 1);
      DBUG_ASSERT(ptr()[0] == 'S' || ptr()[0] == 's');
      return F_PREF_SIGN;
    }
  };


  /********** Rules consisting of 2 token choices ***/

  // decimal_flag: 'B' | '$'
  using Decimal_flag_cond= TokenChoiceCond2<Parser,
                                            TokenID::tB,
                                            TokenID::tDOLLAR>;
  // group_separator: ',' | 'G'
  using Group_separator_cond= TokenChoiceCond2<Parser,
                                               TokenID::tCOMMA,
                                               TokenID::tG>;
  class Group_separator: public TokenChoice<Parser, Group_separator_cond>
  { using TokenChoice::TokenChoice; };


  // zeros_or_nines: zeros | nines
  using Zeros_or_nines_cond= TokenChoiceCond2<Parser,
                                              TokenID::tZEROS,
                                              TokenID::tNINES>;
  class Zeros_or_nines: public TokenChoice<Parser, Zeros_or_nines_cond>
  {
  public:
    using TokenChoice::TokenChoice;
    Zeros_or_nines(Zeros && rhs)
     :TokenChoice(std::move(rhs))
    { }
    Zeros_or_nines(Nines && rhs)
     :TokenChoice(std::move(rhs))
    { }
  };


  /********** Postfix sign ****/

  // postfix_sign: 'S' | 'MI' | 'PR'
  using Postfix_sign_cond= TokenChoiceCond3<Parser,
                                            TokenID::tS,
                                            TokenID::tMI,
                                            TokenID::tPR>;
  class Postfix_sign_signature: public TokenChoice<Parser, Postfix_sign_cond>
  { using TokenChoice::TokenChoice; };


  // postfix_specific_sign: 'MI' | 'PR'
  using Postfix_specific_sign_cond= TokenChoiceCond2<Parser,
                                                     TokenID::tMI,
                                                     TokenID::tPR>;
  class Postfix_specific_sign_signature:
                               public TokenChoice<Parser,
                                                  Postfix_specific_sign_cond>
  { using TokenChoice::TokenChoice; };


  /*
    A container for the postfix sign.
    Depending on the grammar rule, the postfix sign can be:
    - postfix_specific_sign:  MI, PR
    - postfix_sign:           MI, PR, S (all sign variants)
  */
  class Postfix_sign: public LS_container
  {
    using PARENT= LS_container;
  public:
    using PARENT::PARENT;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 1 || length() == 2);
      return F_POST_SIGN;
    }
    // Initializing from rules
    Postfix_sign(Postfix_sign_signature && rhs)
     :PARENT(std::move(static_cast<PARENT&&>(rhs)))
    { }
    Postfix_sign(Postfix_specific_sign_signature && rhs)
     :PARENT(std::move(static_cast<PARENT&&>(rhs)))
    { }
    using Container= CONTAINER1<Parser, Postfix_sign>;
  };


  /*
    positional_currency_signature: 'C' | 'L' | 'U'

    The position of CLU inside the format is important, hence the name.

    Note, the position of the dollar sign is not important, it can be
    specified once on any position inside the number.
  */
  using Positional_currency_signature_cond= TokenChoiceCond3<Parser,
                                                             TokenID::tC,
                                                             TokenID::tL,
                                                             TokenID::tU>;

  // prefix_currency_signature: positional_currency_signature
  class Prefix_currency: public LS_container
  {
  public:
    using LS_container::LS_container;
    class Cond: public Positional_currency_signature_cond { };
    using Container= CONTAINER1<Parser, Prefix_currency>;
    using LParser= TokenChoice<Parser, Cond>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 1);
      DBUG_ASSERT(is_positional_currency((uchar) ptr()[0]));
      return (feature_t) F_PREF_CLU;
    }
  };

  // postfix_currency_signature: positional_currency_signature
  class Postfix_currency: public LS_container
  {
  public:
    using LS_container::LS_container;
    class Cond: public Positional_currency_signature_cond { };
    using Container= CONTAINER1<Parser, Postfix_currency>;
    using LParser= TokenChoice<Parser, Cond>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 1);
      DBUG_ASSERT(is_positional_currency((uchar) ptr()[0]));
      return (feature_t) F_PREF_CLU;
    }
  };

  // dec_delimiter_currency_signature: positional_currency_signature
  class Dec_delimiter_pDVCLU: public LS_container
  {
  public:
    using LS_container::LS_container;
    class Cond: public Positional_currency_signature_cond { };
    using Container= CONTAINER1<Parser, Dec_delimiter_pDVCLU>;
    using LParser= TokenChoice<Parser, Cond>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 1);
      uint res= F_NONE;
      if (is_positional_currency(ptr()[0]))
        return F_FRAC_DEC_CLU;
      switch (ptr()[0]) {
      case '.':
        res|= F_FRAC_DEC_PERIOD;
        break;
      case 'D':
      case 'd':
        res|= F_FRAC_DEC_D;
        break;
      case 'V':
      case 'v':
        res|= F_FRAC_DEC_V;
        break;
      default:
        DBUG_ASSERT(0);
        break;
      }
      return (feature_t) res;
    }
  };


  // format_TM_signature: 'TM' | 'TM9' | 'TME'
  class Format_TM: public LS_container
  {
  public:
    using LS_container::LS_container;
    using Cond= TokenChoiceCond3<Parser, TokenID::tTM,
                                         TokenID::tTM9,
                                         TokenID::tTME>;
    using Container= CONTAINER1<Parser, Format_TM>;
    using LParser= TokenChoice<Parser, Cond>;
    feature_t features() const
    {
      if (!length())
        return F_NONE;
      DBUG_ASSERT(length() == 2 || length() == 3);
      return F_FMT_TM;
    }
  };


  // fraction_pDV_signature: '.' | 'D' | 'V'
  using Fraction_pDV_signature_cond= TokenChoiceCond3<Parser,
                                                      TokenID::tPERIOD,
                                                      TokenID::tD,
                                                      TokenID::tV>;
  class Fraction_pDV_signature: public TokenChoice<Parser,
                                                   Fraction_pDV_signature_cond>
  { using TokenChoice::TokenChoice; };



  // Rules consisting of more complex token choices

  // fractional_element: zeros_or_nines | decimal_flag
  class Fractional_element_cond
  {
  public:
    static bool allowed_token_id(TokenID id)
    {
      return Zeros_or_nines_cond::allowed_token_id(id) ||
             Decimal_flag_cond::allowed_token_id(id);
    }
  };
  class Fractional_element: public TokenChoice<Parser, Fractional_element_cond>
  { using TokenChoice::TokenChoice; };


  // integer_element: fractional_element | group_separator
  class Integer_element_cond
  {
  public:
    static bool allowed_token_id(TokenID id)
    {
      return Fractional_element_cond::allowed_token_id(id) ||
             Group_separator_cond::allowed_token_id(id);
    }
  };
  class Integer_element: public TokenChoice<Parser, Integer_element_cond>
  { using TokenChoice::TokenChoice; };



  /*
    Rules consisting of a LIST of token choices
  */

  // currency_prefix_flag: decimal_flag
  // currency_prefix_flags: currency_prefix_flag [ currency_prefix_flag...]
  class Currency_prefix_flags: public LS_container
  {
  public:
    using LS_container::LS_container;
    Decimal_flag_counters prefix_flag_counters() const
    {
      Decimal_flag_counters tmp;
      for (size_t i= 0; i < length(); i++)
        tmp.add(ptr()[i]);
      return tmp;
    }
    using Container= CONTAINER1<Parser, Currency_prefix_flags>;
    using Flag= TokenChoice<Parser, Decimal_flag_cond>;
    using LParser= LIST<Parser, Container, Flag,
                        TokenID::tNULL /* not separated */,
                        1 /* needs at list one element */>;
    feature_t features() const
    {
      DBUG_ASSERT(length() <= 2); // $ + B
      uint res= F_NONE;
      for (size_t i= 0; i < length(); i++)
      {
        switch (ptr()[i]) {
        case '$':
          res|= F_PREF_DOLLAR;
          break;
        case 'B':
        case 'b':
          res|= F_PREF_B;
          break;
        default:
          DBUG_ASSERT(0);
          break;
        }
      }
      return (feature_t) res;
    }
  };


  /*
    Digits:
    - decimal digit placeholders: 0 9
    - hex digit placeholders:     X    (only in the integer part of a number)
    - inline flags:               $ B
    - group separators:           , G  (only in the integer part of a number)
  */
  class Digits: public LS_container,
                public Decimal_flag_counters
  {
    using A= LS_container;
    using B= Decimal_flag_counters;
  public:
    using Container= OR_CONTAINER2<Parser, Digits, A, B>;
    // Initializing from its components
    Digits(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }
    // Initializing from rules
    Digits(Zeros_or_nines && rhs)
     :A(std::move(rhs))
    { }
    Digits(XChain && rhs)
     :A(std::move(rhs))
    { }

    // Other methods
    bool check_counters() const
    {
      /*
        - $ can appear only once
        - B can appear only once
        - Comma and G cannot co-exist
      */
      return m_dollar_count > 1 || m_B_count > 1 ||
             (m_comma_count > 0 && m_G_count > 0);
    }
    operator bool() const
    {
      return LS_container::operator bool() && !check_counters();
    }

    /*
      Hide the inherited concat() to prevent descendants from using it
      in a mistake instead of join().
    */
    bool concat()= delete;
    bool join(Digits && rhs)
    {
      B::join(std::move(rhs));
      return A::concat(std::move(rhs));
    }
    bool add(Parser *p, const Lex_cstring && rhs) // for LIST
    {
      DBUG_ASSERT(rhs.length > 0);
      B::add(rhs.str[0]);
      if (check_counters())
        return true;
      return A::add(p, std::move(rhs));
    }

  }; // End of class Digits



  /********** Rules related to the integer part of a number ***/

  // integer: integer_element [ integer_element...]
  class Integer: public Digits::Container
  {
    using PARENT= Digits::Container;
    using SELF= Integer;
  public:
    using Container= CONTAINER1<Parser, Integer>;
    using PARENT::PARENT;

    // Helper constructors used in descendants
    Integer(Zeros_or_nines && zn, XChain && xchain)
     :PARENT(std::move(zn))
    {
      // XChain cannot have flags/group, Ok to call concat instead of join.
      LS_container::concat(std::move(xchain));
    }

    // Zeros_or_nines + extra digits
    Integer(Zeros_or_nines && head, Integer && tail)
     :PARENT(std::move(head))
    {
      SELF::join(std::move(tail));
    }

    /*
      A tail of an integer number.
      It can start with a group character.
    */
    using Tail= LIST<Parser, Container,
                     Integer_element,
                     TokenID::tNULL /*not separated*/,
                     1 /* needs at least one element*/>;

    // Other methods

    // Convert to a number in case there is no G character in the format
    Double_null to_dbln_no_G(LS sbj, CHARSET_INFO *cs) const
    {
      DBUG_ASSERT(m_G_count == 0);
      size_t flag_count= m_dollar_count + m_B_count;
      sbj= sbj.ltrim(cs);
      DBUG_ASSERT(flag_count <= length());
      // $ and B are flags, they don't need to match anything in sbj
      size_t chars_to_match= length() - flag_count;
      if (chars_to_match < sbj.length())
        return Double_null(); // Can never match

      /*
        Skip the leading format characters which require a match in
        the subject string (i.e. digits and commas) and which are outside
        of the subject length.
          sbj='12, fmt= '$99B9' -> fmt= '9B9'
      */
      size_t skip= chars_to_match - sbj.length();
      const char *fmt;
      for (fmt= ptr(); fmt < end() && skip > 0; fmt++)
      {
        if (!is_currency_flag(*fmt))
          skip--;
      }
      DBUG_ASSERT(((size_t)(end() - fmt)) >= sbj.length());

      double nr= 0;
      size_t digit_matched= 0;
      for (size_t pos= 0; pos < sbj.length(); pos++, fmt++)
      {
        fmt= LS(fmt, end()).ltrim_currency_flags().ptr();
        if (*fmt == ',')
        {
          if (sbj.ptr()[pos] != ',')
            return Double_null();
          continue;
        }
        DBUG_ASSERT(*fmt == '0' || *fmt == '9');
        if (sbj.ptr()[pos] < '0' && sbj.ptr()[pos] > '9')
          return Double_null();
        digit_matched++;
        nr*= 10;
        nr+= ((uint) (uchar) sbj.ptr()[pos]) - (uchar) '0';
      }
      DBUG_ASSERT(LS(fmt, end()).ltrim_currency_flags().ptr() == end());

      return digit_matched ? Double_null(nr) : Double_null();
    }

    feature_t features() const
    {
      uint res= F_NONE;
      if (length() > flag_length())
      {
        res|= F_INT_DIGIT;
        if (end()[-1] == 'X' || end()[-1] == 'x')
          res|= F_INT_HEX;
      }
      if (m_B_count)
        res|= F_INT_B;
      if (m_dollar_count)
        res|= F_INT_DOLLAR;
      if (m_comma_count)
        res|= F_INT_GROUP_COMMA;
      if (m_G_count)
        res|= F_INT_GROUP_G;
      return (feature_t) res;
    }

  };



  /********** Rules related to the fractional part of a number ***/

  // fraction_body: fractional_digit [ fractional_digit ... ]
  class Fraction_body: public Digits::Container
  {
    using PARENT= Digits::Container;
  public:
    using PARENT::PARENT;
    using Container= CONTAINER1<Parser, Fraction_body>;
    using LParser= LIST<Parser, Fraction_body::Container, Fractional_element,
                        TokenID::tNULL /* not separated */, 1>;
    feature_t features() const
    {
      uint res= F_NONE;
      if (length() > flag_length())
        res|= F_FRAC_DIGIT;
      if (m_B_count)
        res|= F_FRAC_B;
      if (m_dollar_count)
        res|= F_FRAC_DOLLAR;
      return (feature_t) res;
    }
  };


  /*
    fraction_pDVCLU: positional_currency [ fraction_body ]
     | fraction_pDV_signature [ fraction_body ] [ postfix_currency_signature ]
  */

  class Fraction: public Dec_delimiter_pDVCLU::Container,
                  public Fraction_body::Container,
                  public Postfix_currency::Container
  {
    using A= Dec_delimiter_pDVCLU::Container;
    using B= Fraction_body::Container;
    using C= Postfix_currency::Container;
  public:
    using Container= OR_CONTAINER3<Parser, Fraction, A, B, C>;

    size_t length() const
    {
      return A::length() + B::length() +  C::length();
    }

    feature_t features() const
    {
      return (feature_t) (A::features() | B::features() |  C::features());
    }

    // Initialization from its components
    Fraction(A && a, B && b, C && c)
     :A(std::move(a)), B(std::move(b)), C(std::move(c))
    { }

    // Sub-component rules
    class pDV: public AND2<Parser,
                           Fraction_pDV_signature,
                           Fraction_body::LParser::Opt>
    {
    public:
      using AND2::AND2;
      // TODO: make LIST provide empty()
      static pDV empty(const Parser &parser)
      {
        return pDV(Fraction_pDV_signature::empty(parser),
                   Fraction_body::Container::empty(parser));
      }
    };

  private:
    class pDVCLU_signature_Opt_Fraction_body:
                                    public AND2<Parser,
                                                Dec_delimiter_pDVCLU::LParser,
                                                Fraction_body::LParser::Opt>
    { using AND2::AND2; };
    class pDV_signature_Opt_Fraction_body_Opt_Postfix_currency:
                                    public AND3<Parser,
                                                Fraction_pDV_signature,
                                                Fraction_body::LParser::Opt,
                                                Postfix_currency::LParser::Opt>
    { using AND3::AND3; };
  public:

    // Initialization from rules
    Fraction(pDV && rhs)
     :A(std::move(static_cast<Fraction_pDV_signature&&>(rhs))),
      B(std::move(static_cast<Fraction_body::Container&&>(rhs))),
      C(C::empty())
    { }

    /*
      TODO: Opt_fraction_body can return true while
      Fraction_body::Container after initialization from it
      (from its Opt_fraction_body::Fraction_body::Container actually)
      can return false.
    */
    Fraction(pDVCLU_signature_Opt_Fraction_body && rhs)
     :A(std::move(static_cast<Dec_delimiter_pDVCLU::LParser&&>(rhs))),
      B(std::move(static_cast<Fraction_body::LParser::Opt&&>(rhs))),
      C(C::empty())
    { }

    Fraction(pDV_signature_Opt_Fraction_body_Opt_Postfix_currency && rhs)
     :A(std::move(static_cast<Fraction_pDV_signature&&>(rhs))),
      B(std::move(static_cast<Fraction_body::Container&&>(rhs))),
      C(std::move(static_cast<Postfix_currency::LParser::Opt&&>(rhs)))
    { }


    using LParser= OR2C<Parser, Fraction::Container,
                        pDVCLU_signature_Opt_Fraction_body,
                        pDV_signature_Opt_Fraction_body_Opt_Postfix_currency>;


  };



  /********** A tail of a decimal number ***/

  /*
    decimal_tail_pDVCLU: integer_tail [ fraction_pDVCLU ]
                       | fraction_pDVCLU

    decimal_tail_pDV: integer_tail [ fraction_pDV ]
                    | fraction_pDV
  */

  class Decimal_tail: public Integer::Container,
                      public Fraction::Container
  {
    using A= Integer::Container;
    using B= Fraction::Container;
  public:
    using Container= OR_CONTAINER2<Parser, Decimal_tail,
                                   Integer::Container,
                                   Fraction::Container>;
    // Initializing from its componenets
    Decimal_tail(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }

    // Dependency rules
private:
    using Integer_tail_Opt_Fraction_pDVCLU= AND2<Parser,
                                                 Integer::Tail,
                                                 Fraction::LParser::Opt>;

    using Integer_tail_Opt_Fraction_pDV= AND2<Parser,
                                              Integer::Tail,
                                              Fraction::pDV::Opt>;
public:

    // Initializing from rules
    Decimal_tail(Integer_tail_Opt_Fraction_pDVCLU && rhs)
     :A(std::move(rhs)), B(std::move(rhs))
    { }
    Decimal_tail(Integer_tail_Opt_Fraction_pDV && rhs)
     :A(std::move(rhs)), B(std::move(rhs))
    { }

    Decimal_tail(Fraction::LParser && rhs)
     :A(A::empty()), B(std::move(rhs))
    { }
    Decimal_tail(Fraction::pDV && rhs)
     :A(A::empty()), B(std::move(rhs))
    { }

    // Derived rules
    using Tail_pDVCLU= OR2C<Parser, Container,
                            Integer_tail_Opt_Fraction_pDVCLU,
                            Fraction::LParser>;

    using Tail_pDV= OR2C<Parser, Container,
                         Integer_tail_Opt_Fraction_pDV,
                         Fraction::pDV>;
  };



  /********** A decimal number ****/

  class Decimal: public Decimal_tail::Container
  {
    using PARENT= Decimal_tail::Container;
  public:
    using PARENT::PARENT;
    using Container= CONTAINER1<Parser, Decimal>;

    // Initializing from rules
    Decimal(XChain && rhs)
     :PARENT(std::move(rhs), Fraction::Container::empty())
    { }

    // Helper constructors used in descendants
    Decimal(Zeros_or_nines && head, Decimal_tail && tail)
     :PARENT(
        Integer::Container(std::move(head),
                          std::move(static_cast<Integer::Container&&>(tail))),
        std::move(static_cast<Fraction::Container&&>(tail)))
    { }

  };


  /********** A tail of an approximate number (scientific notation) ***/

  /*
    An approximate tail:
    Its integer part can start with a group character.

    approximate_tail_pDVCLU: decimal_tail_pDVCLU [ EEEE ]
                           | EEEE
    approximate_tail_pDV: decimal_tail_pDV [ EEEE ]
                        | EEEE
  */
  class Approximate_tail: public Decimal_tail::Container,
                          public EEEE::Container
  {
    using A= Decimal_tail::Container;
    using B= EEEE::Container;
  public:
    using Container= OR_CONTAINER2<Parser, Approximate_tail, A, B>;
    feature_t features() const
    {
      return (feature_t) (Integer::features() |
                          Fraction::features() |
                          EEEE::features());
    }

    // Initialization from its components
    Approximate_tail(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }

    // Dependency rules
private:
    using Decimal_tail_pDVCLU_Opt_EEEE= AND2<Parser,
                                             Decimal::Tail_pDVCLU,
                                             EEEE::LParser::Opt>;
    using Decimal_tail_pDV_Opt_EEEE= AND2<Parser,
                                          Decimal::Tail_pDV,
                                          EEEE::LParser::Opt>;
public:
    // Initialization from rules
    Approximate_tail(EEEE::LParser::Opt && rhs)
     :A(A::empty()), B(std::move(rhs))
    { }
    Approximate_tail(Decimal_tail_pDVCLU_Opt_EEEE && rhs)
     :A(std::move(static_cast<Decimal::Tail_pDVCLU&&>(rhs))),
      B(std::move(static_cast<EEEE::LParser::Opt&&>(rhs)))
    { }
    Approximate_tail(Decimal_tail_pDV_Opt_EEEE && rhs)
     :A(std::move(static_cast<Decimal::Tail_pDV&&>(rhs))),
      B(std::move(static_cast<EEEE::LParser::Opt&&>(rhs)))
    { }
    Approximate_tail(XChain && rhs)
     :A(std::move(rhs)), B(B::empty())
    { }
    Approximate_tail(Fraction::pDV && rhs)
     :A(std::move(rhs)), B(B::empty())
    { }
    Approximate_tail(Fraction::LParser && rhs)
     :A(std::move(rhs)), B(B::empty())
    { }

    // Derived rules
    using Tail_pDVCLU= OR2C<Parser, Container,
                            Decimal_tail_pDVCLU_Opt_EEEE,
                            EEEE::LParser::Opt>;

    using Tail_pDV= OR2C<Parser, Container,
                         Decimal_tail_pDV_Opt_EEEE,
                         EEEE::LParser::Opt>;
  };


  /********** A well formed approximate number ***/
  /*
    Its integer part starts with a valid element (a digit or a flag).
    It cannot start with a group character.

    approximate_pDVCLU: zero_or_nines [ approximate_tail_pDVCLU ]
                      | fraction_pDVCLU

    approximate_pDV: zero_or_nines [ approximate_tail_pDV ]
                   | fraction_pDV
  */

  class Approximate: public Approximate_tail::Container
  {
    using PARENT= Approximate_tail::Container;
    using SELF= Approximate;
  public:
    using PARENT::PARENT;
    using Container= CONTAINER1<Parser, Approximate>;

    // Dependency rules
private:
    using Zeros_or_nines_Opt_approximate_tail_pDVCLU=
                                       AND2<Parser,
                                            Zeros_or_nines,
                                            Approximate_tail::Tail_pDVCLU::Opt>;

    using Zeros_or_nines_Opt_approximate_tail_pDV=
                                          AND2<Parser,
                                               Zeros_or_nines,
                                               Approximate_tail::Tail_pDV::Opt>;

protected:
    // Dependency rules, also used by Unsigned_currency
    using Nines_Opt_approximate_tail_pDVCLU=
                                      AND2<Parser,
                                           Nines,
                                           Approximate_tail::Tail_pDVCLU::Opt>;

    using Zeros_Opt_approximate_tail_pDVCLU=
                                       AND2<Parser,
                                            Zeros,
                                            Approximate_tail::Tail_pDVCLU::Opt>;
public:

    // Initializing from rules
    Approximate(Zeros_Opt_approximate_tail_pDVCLU && rhs)
     :PARENT(
       Decimal::Container(
         std::move(static_cast<Zeros &&>(rhs)),
         std::move(static_cast<Decimal_tail::Container &&>(rhs))),
       std::move(static_cast<EEEE::Container&&>(rhs)))
    {  }

    Approximate(Nines_Opt_approximate_tail_pDVCLU && rhs)
     :PARENT(
       Decimal::Container(std::move(static_cast<Nines &&>(rhs)),
                         std::move(static_cast<Decimal_tail::Container &&>(rhs))),
       std::move(static_cast<EEEE::Container&&>(rhs)))
    { }

    Approximate(Zeros_or_nines_Opt_approximate_tail_pDVCLU && rhs)
     :PARENT(
       Decimal::Container(
         std::move(static_cast<Zeros_or_nines &&>(rhs)),
         std::move(static_cast<Decimal_tail::Container &&>(rhs))),
       std::move(static_cast<EEEE::Container&&>(rhs)))
    { }

    Approximate(Zeros_or_nines_Opt_approximate_tail_pDV && rhs)
     :PARENT(
       Decimal::Container(
         std::move(static_cast<Zeros_or_nines &&>(rhs)),
         std::move(static_cast<Decimal_tail::Container &&>(rhs))),
       std::move(static_cast<EEEE::Container&&>(rhs)))
    { }

    // Derived rules
    using pDVCLU= OR2C<Parser, Container,
                       Zeros_or_nines_Opt_approximate_tail_pDVCLU,
                       Fraction::LParser>;

    using pDV= OR2C<Parser, Container,
                    Zeros_or_nines_Opt_approximate_tail_pDV,
                    Fraction::pDV>;

    // Misc
    void print(String *str) const
    {
      DBUG_ASSERT(Dec_delimiter_pDVCLU::length() ||
                  !Fraction_body::Container::length());
      str->append("A='"_LS);
      Integer::Container::print(str);
      if (Dec_delimiter_pDVCLU::length())
      {
        str->append("["_LS);
        Dec_delimiter_pDVCLU::print(str);
        str->append("]"_LS);
      }
      Fraction_body::Container::print(str);
      str->append("'"_LS);
      if (Postfix_currency::length())
      {
        str->append("RC='"_LS);
        Postfix_currency::print(str);
        str->append("'"_LS);
      }
      EEEE::print(str);
    }
  };


  /********** Rules related to a number with a prefix currency signature ***/

  /*
      lflagged_approximate: 'B' approximate_pDV
  */
  class LFlagged_approximate: public Currency_prefix_flags::Container,
                              public Approximate::Container
  {
    using A= Currency_prefix_flags::Container;
    using B= Approximate::Container;
  public:
    using Container= OR_CONTAINER2<Parser, LFlagged_approximate, A, B>;
    // Initialization from its components
    LFlagged_approximate(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }
    // Dependency rules
    using B_Opt_Approximate_pDV= AND2<Parser, TokenB, Approximate::pDV::Opt>;
    // Initialization from rules
    LFlagged_approximate(B_Opt_Approximate_pDV && rhs)
     :A(std::move(static_cast<TokenB&&>(rhs))),
      B(std::move(static_cast<Approximate::Container&&>(rhs)))
    { }
    LFlagged_approximate(Approximate::pDV && rhs)
     :A(A::empty()),
      B(std::move(rhs))
    { }
  };


  /********** Unsigned currency ***/

  /*
    unsigned_currency: unsigned_currency0
                     | unsigned_currency1

    usigned_currency0: zeros [ approximate_tail_pDVCLU ];

    Unsigned_currency1 - a currency not starting with zeros:

    unsigned_currency1:
        nines  [ approximate_tail_pDVCLU ]
      | decimal_flags [ approximate_pDVCLU ]
      | left_currency
      | fraction_pDV [EEEE] [ positional_currency ]


    left_currency: prefix_currency_signature     [ approximate_pDV ]
                 | prefix_currency_signature 'B' [ approximate_pDV ]
  */

  class Unsigned_currency: public Prefix_currency::Container,
                           public Currency_prefix_flags::Container,
                           public Approximate::Container
  {
    using A= Prefix_currency::Container;
    using B= Currency_prefix_flags::Container;
    using C= Approximate::Container;
  public:
    using Container= OR_CONTAINER3<Parser, Unsigned_currency, A, B, C>;
    feature_t features() const
    {
      return (feature_t) (A::features() | B::features() | C::features());
    }

    // Initializing from its componenents
    Unsigned_currency(A && a, B && b, C && c)
     :A(std::move(a)), B(std::move(b)), C(std::move(c))
    { }
    // Dependency rules
private:
    using Left_currency_tail= OR2C<Parser, LFlagged_approximate::Container,
                                   Approximate::pDV,
                                   LFlagged_approximate::B_Opt_Approximate_pDV>;

    using Left_currency= AND2<Parser,
                              Prefix_currency::LParser,
                              Left_currency_tail::Opt>;

    using Decimal_flags_Opt_approximate_pDVCLU=
                                         AND2<Parser,
                                              Currency_prefix_flags::LParser,
                                              Approximate::pDVCLU::Opt>;

    using Fraction_pDV_Opt_EEEE_Opt_postfix_currency=
                                           AND3<Parser,
                                                Fraction::pDV,
                                                EEEE::LParser::Opt,
                                                Postfix_currency::LParser::Opt>;
public:
    // Initializing from rules
    Unsigned_currency(Nines_Opt_approximate_tail_pDVCLU &&rhs)
     :A(A::empty()),
      B(B::empty()),
      C(std::move(rhs))
    { }
    Unsigned_currency(Decimal_flags_Opt_approximate_pDVCLU &&rhs)
     :A(A::empty()),
      B(std::move(static_cast<Currency_prefix_flags::LParser&&>(rhs))),
      C(std::move(static_cast<Approximate::Container&&>(rhs)))
    { }
    Unsigned_currency(Left_currency &&rhs)
     :A(std::move(static_cast<Prefix_currency::LParser&&>(rhs))),
      B(std::move(static_cast<Currency_prefix_flags::Container&&>(rhs))),
      C(std::move(static_cast<Approximate::Container&&>(rhs)))
    { }
    Unsigned_currency(Fraction_pDV_Opt_EEEE_Opt_postfix_currency &&rhs)
     :A(A::empty()),
      B(B::empty()),
      C(Fraction::Container(
          std::move(static_cast<Fraction_pDV_signature&&>(rhs)),
          std::move(static_cast<Fraction_body::LParser::Opt&&>(rhs)),
          std::move(static_cast<Postfix_currency::LParser::Opt&&>(rhs))),
        EEEE::Container(std::move(static_cast<EEEE::LParser::Opt&&>(rhs))))
    { }
    Unsigned_currency(Zeros_Opt_approximate_tail_pDVCLU && rhs)
     :A(A::empty()),
      B(B::empty()),
      C(std::move(rhs))
    { }

    using Unsigned_currency0= Zeros_Opt_approximate_tail_pDVCLU;

    using Unsigned_currency1= OR4C<Parser, Container,
                                   Nines_Opt_approximate_tail_pDVCLU,
                                   Decimal_flags_Opt_approximate_pDVCLU,
                                   Left_currency,
                                   Fraction_pDV_Opt_EEEE_Opt_postfix_currency>;

    using LParser= OR2C<Parser, Container,
                        Unsigned_currency0,
                        Unsigned_currency1>;


  };


  /********** A currency with a postfix sign ***/
  /*
    For the grammar simplicity, currency0_with_postfix_sign includes
    xchain (optionally preceding by zeros), allthough it cannot really
    be followed by a postfix sign. "xxx_with_postix_sign" here means
    "xxx which can optionally be followed by a postfix sign", or
    "xxx which does not have a preceeding prefix sign".


    currency0_with_postfix_sign: zeros xchain
                           | zeros [ approximate_tail_pDVCLU ] [ postfix_sign ]
    Rewriting as:
    zeros [ zeros_tail ]
    zeros_tail: xchain
              | approximate_tail_pDVCLU [ postfix_sign ]
              | postfix_sign
  */

  class Currency0_tail_with_postfix_sign: public Approximate_tail::Container,
                                          public Postfix_sign::Container
  {
    using A= Approximate_tail::Container;
    using B= Postfix_sign::Container;
  public:
    using Container= OR_CONTAINER2<Parser, Currency0_tail_with_postfix_sign,
                                   A, B>;
    // Initialization from its componebts
    Currency0_tail_with_postfix_sign(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }

    // Dependency rules
  private:
    using Approximate_tail_pDVCLU_Opt_postfix_sign=
                                             AND2<Parser,
                                                  Approximate_tail::Tail_pDVCLU,
                                                  Postfix_sign_signature::Opt>;
  public:
    // Initialization from rules
    Currency0_tail_with_postfix_sign(XChain && rhs)
     :A(std::move(rhs)), B(B::empty())
    { }
    Currency0_tail_with_postfix_sign(
                                Approximate_tail_pDVCLU_Opt_postfix_sign &&rhs)
     :A(std::move(static_cast<Approximate_tail::Container&&>(rhs))),
      B(std::move(static_cast<Postfix_sign_signature::Opt&&>(rhs)))
    { }
    Currency0_tail_with_postfix_sign(Postfix_sign_signature::Opt && rhs)
     :A(A::empty()), B(std::move(rhs))
    { }

    using LParser=OR3C<Parser, Currency0_tail_with_postfix_sign::Container,
                       XChain,
                       Approximate_tail_pDVCLU_Opt_postfix_sign,
                       Postfix_sign_signature::Opt>;
  };


  /*
    currency_with_postfix_sign: xchain
                      | currency0_with_postfix_sign
                      | unsigned_currency1 [ postfix_sign ]
                      | postfix_specific_sign
  */
  class Currency_with_postfix_sign: public Unsigned_currency::Container,
                                    public Postfix_sign::Container
  {
    using A= Unsigned_currency::Container;
    using B= Postfix_sign::Container;
  public:
    using Container= OR_CONTAINER2<Parser, Currency_with_postfix_sign, A, B>;
    feature_t features() const
    {
      return (feature_t) (Postfix_sign::features() |
                          Unsigned_currency::features());
    }
    // Initialization from its components
    Currency_with_postfix_sign(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }

    // Dependency rules
private:
    using Currency0_with_postfix_sign=
                                AND2<Parser,
                                     Zeros,
                                     Currency0_tail_with_postfix_sign::LParser>;

    using Unsigned_currency1_Opt_Postfix_sign=
                                     AND2<Parser,
                                          Unsigned_currency::Unsigned_currency1,
                                          Postfix_sign_signature::Opt>;
public:
    // Initialization from rules
    Currency_with_postfix_sign(XChain && rhs)
     :A(Approximate::Container(std::move(rhs))),
      B(B::empty())
    { }

    Currency_with_postfix_sign(Currency0_with_postfix_sign && rhs)
     :A(Approximate::Container(
          Decimal::Container(
            std::move(static_cast<Zeros&&>(rhs)),
            std::move(static_cast<Approximate_tail::Container&&>(rhs))))),
      B(std::move(static_cast<Postfix_sign::Container&&>(rhs)))
    { }

    Currency_with_postfix_sign(Unsigned_currency1_Opt_Postfix_sign && rhs)
     :A(std::move(static_cast<Unsigned_currency::Container&&>(rhs))),
      B(std::move(static_cast<Postfix_sign_signature::Opt&&>(rhs)))
    { }

    Currency_with_postfix_sign(Postfix_specific_sign_signature && rhs)
     :A(A::empty()),
      B(std::move(rhs))
    { }

    using LParser= OR4C<Parser, Currency_with_postfix_sign::Container,
                        XChain,
                        Currency0_with_postfix_sign,
                        Unsigned_currency1_Opt_Postfix_sign,
                        Postfix_specific_sign_signature>;

    // Other methods
    bool check(const Parser & parser,
               Sql_state_errno_level::enum_warning_level level,
               const Decimal_flag_counters & prefix_flag_counters) const
    {
      // '$9C'  '9$C'
      if (prefix_flag_counters.m_dollar_count ||
          Integer::Container::m_dollar_count ||
          Fraction::Container::m_dollar_count)
      {
        if (Dec_delimiter_pDVCLU::length())
        {
          const char *dec= Dec_delimiter_pDVCLU::ptr();
          if (is_positional_currency(dec[0]))
          {
            parser.parse_error_at(current_thd, level, dec);
            return true;
          }
        }
        // '$.C'
        if (Postfix_currency::length())
        {
          parser.parse_error_at(current_thd, level,
                                Postfix_currency::ptr());
          return true;
        }
      }

      // 'C0$', 'C$U' 'V$U'
      if (Prefix_currency::length() &&
          (Integer::Container::m_dollar_count ||
           Fraction::Container::m_dollar_count))
      {
        // TODO: better position
        parser.parse_error_at(current_thd, level, Prefix_currency::end());
        return true;
      }

      // '$.$'  'B.B'
      if (prefix_flag_counters.m_dollar_count +
          Integer::Container::m_dollar_count +
          Fraction::Container::m_dollar_count > 1 ||
          prefix_flag_counters.m_B_count +
          Integer::Container::m_B_count +
          Fraction::Container::m_B_count > 1)
      {
        // TODO: better position
        parser.parse_error_at(current_thd, level, parser.buffer().str);
        return true;
      }

      if (Integer::Container::length() == 0 && EEEE::length() != 0)
      {
        parser.parse_error_at(current_thd, level, EEEE::ptr());
        return true;
      }

      return false;
    }

    void print(String *str) const
    {
      if (Currency_prefix_flags::Container::length())
      {
        str->append("CFl='"_LS);
        Currency_prefix_flags::Container::print(str);
        str->append("'"_LS);
      }

      if (Prefix_currency::length())
      {
        str->append("LC='"_LS);
        Prefix_currency::print(str);
        str->append("'"_LS);
      }

      Approximate::Container::print(str);

      if (Postfix_sign::Container::length())
      {
        str->append("RS='"_LS);
        Postfix_sign::Container::print(str);
        str->append("'"_LS);
      }
    }


  };


  /********** An unsigned format ***/

  /*
    unsigned_format: unsigned_currency
                   | format_TM_signature
  */

  class Unsigned_format: public Unsigned_currency::Container,
                         public Format_TM::Container
  {
    using A= Unsigned_currency::Container;
    using B= Format_TM::Container;
  public:
    using Container= OR_CONTAINER2<Parser, Unsigned_format, A, B>;

    // Initializing from its componenet
    Unsigned_format(A && a, B && b)
     :A(std::move(a)), B(std::move(b))
    { }

    // Initilizing from rules
    Unsigned_format(Unsigned_currency::LParser && rhs)
     :A(std::move(rhs)), B(B::empty())
    { }

    Unsigned_format(Format_TM::LParser && rhs)
     :A(A::empty()), B(std::move(rhs))
    { }
    using LParser= OR2C<Parser, Container,
                        Unsigned_currency::LParser,
                        Format_TM::LParser>;
  };


  /********** The format - the top level rules ****/

  /*
    format_FM_tail: currency_with_postfix_sign
                  | 'S' [ unsigned_format ]

  */


  class Format_FM_tail: public Prefix_sign::Container,
                        public Unsigned_format::Container,
                        public Postfix_sign::Container
  {
    using A= Prefix_sign::Container;
    using B= Unsigned_format::Container;
    using C= Postfix_sign::Container;
  public:
    using Container= OR_CONTAINER3<Parser, Format_FM_tail, A, B, C>;

    // Initialization from its components
    Format_FM_tail(A && a, B && b, C && c)
     :A(std::move(a)), B(std::move(b)), C(std::move(c))
    { }

    // Dependency rules
private:
    using Prefix_sign_Opt_unsigned_format= AND2<Parser,
                                                Prefix_sign::LParser,
                                                Unsigned_format::LParser::Opt>;
public:
    // Initializing from rules
    Format_FM_tail(Format_TM::LParser &&rhs)
     :A(A::empty()),
      B(Format_TM::Container(std::move(rhs))),
      C(C::empty())
    { }

    Format_FM_tail(Currency_with_postfix_sign::LParser && rhs)
     :A(A::empty()),
      B(static_cast<Unsigned_currency::Container&&>(rhs)),
      C(std::move(static_cast<Postfix_sign::Container&&>(rhs)))
    { }

    Format_FM_tail(Prefix_sign_Opt_unsigned_format && rhs)
     :A(std::move(static_cast<Prefix_sign::LParser&&>(rhs))),
      B(std::move(static_cast<Unsigned_format::Container&&>(rhs))),
      C(C::empty())
    { }

    using LParser= OR3C<Parser, Container,
                        Format_TM::LParser,
                        Prefix_sign_Opt_unsigned_format,
                        Currency_with_postfix_sign::LParser>;
  };


  /*
    format: currency_with_postfix_sign
          | 'FM' [ format_FM_tail ]
          | 'S' ['FM'] [ unsigned_format ]
          | postfix_specific_sign
  */
  class Format: public Format_flags::Container,
                public Prefix_sign::Container,
                public Currency_with_postfix_sign::Container,
                public Format_TM::Container
  {
    using A= Format_flags::Container;
    using B= Prefix_sign::Container;
    using C= Currency_with_postfix_sign::Container;
    using D= Format_TM::Container;
  public:
    using Container= OR_CONTAINER4<Parser, Format, A, B, C, D>;
    feature_t features() const
    {
      return (feature_t) (A::features() | B::features() |
                          C::features() | D::features());
    };

    // Initialization from its components
    Format(A && a, B && b, C && c, D && d)
     :A(std::move(a)), B(std::move(b)), C(std::move(c)), D(std::move(d))
    { }

    // Dependency rules
private:
    using Format_FM_xxx= AND2<Parser,
                              Format_flags::LParser,
                              Format_FM_tail::LParser::Opt>;

    using Format_prefix_sign_Opt_FM_Opt_unsigned_format=
                                            AND3<Parser,
                                                 Prefix_sign::LParser,
                                                 Format_flags::LParser::Opt,
                                                 Unsigned_format::LParser::Opt>;
public:
    // Initialization from rules
    Format(Format_FM_xxx && rhs)
     :A(std::move(static_cast<Format_flags::LParser&&>(rhs))),
      B(std::move(static_cast<Prefix_sign::Container&&>(rhs))),
      C(std::move(static_cast<Unsigned_currency::Container&&>(rhs))),
      D(std::move(static_cast<Format_TM::Container&&>(rhs)))
    { }

    Format(Format_prefix_sign_Opt_FM_Opt_unsigned_format && rhs)
     :A(std::move(static_cast<Format_flags::LParser::Opt&&>(rhs))),
      B(std::move(static_cast<Prefix_sign::LParser&&>(rhs))),
      C(std::move(static_cast<Unsigned_currency::Container&&>(rhs))),
      D(std::move(static_cast<Format_TM::Container&&>(rhs)))
    { }

    Format(Postfix_specific_sign_signature && rhs)
     :A(A::empty()),
      B(B::empty()),
      C(std::move(rhs)),
      D(D::empty())
    { }

    Format(Format_TM::LParser && rhs)
     :A(A::empty()),
      B(B::empty()),
      C(C::empty()),
      D(Format_TM::Container(std::move(rhs)))
    { }


    void print(String *str) const
    {
      if (Format_flags::length() > 0)
      {
        str->append("FFl='"_LS);
        Format_flags::print(str);
        str->append("'"_LS);
      }

      if (Prefix_sign::length() > 0)
      {
        str->append("LS='"_LS);
        Prefix_sign::print(str);
        str->append("'"_LS);
      }

      if (Currency_with_postfix_sign::Container::operator bool())
        Currency_with_postfix_sign::Container::print(str);

      if (Format_TM::Container::length())
      {
        str->append("TM='"_LS);
        Format_TM::Container::print(str);
        str->append("'"_LS);
      }
    }

    void print_as_note() const
    {
      StringBuffer<64> tmp;
      print(&tmp);
      push_warning_printf(current_thd, Sql_condition::WARN_LEVEL_NOTE,
                          ER_UNKNOWN_ERROR,
                          "%.*s", (int) tmp.length(), tmp.ptr());
    }

    bool check(const Parser & parser,
               Sql_state_errno_level::enum_warning_level level) const
    {
      if (Currency_with_postfix_sign::Container::operator bool() &&
          Currency_with_postfix_sign::check(parser, level,
                                            prefix_flag_counters()))
        return true;

      return false;
    }


    using LParser= OR5C<Parser, Container,
                        Currency_with_postfix_sign::LParser,
                        Format_FM_xxx,
                        Format_prefix_sign_Opt_FM_Opt_unsigned_format,
                        Format_TM::LParser,
                        Postfix_specific_sign_signature>;
  };


public:
  // goal: [ format ] EOF
  class Goal: public AND2<Parser, Format::LParser::Opt, TokenEOF>
  {
  public:
    using AND2::AND2;
    Goal & operator=(Goal && rhs)
    {
      AND2::operator=(std::move(rhs));
      return *this;
    }
    bool check(const Parser & parser,
               Sql_state_errno_level::enum_warning_level level) const
    {
      if (!operator bool())
      {
        parser.parse_error_at(current_thd, level);
        return true;
      }
      return Format::check(parser, level);
    }
  };
};


class Item_func_to_number: public Item_handled_func
{
  /*
    Structures used to cache the format if args[1] is an evaluable
    constant during fix_length_and_dec_time.
  */
  Format_parser::Goal m_format;
  Format_parser m_parser;
  StringBuffer<32> m_format_buffer;
public:
  Item_func_to_number(THD *thd, List<Item> &list)
   :Item_handled_func(thd, list)
  { }
  LEX_CSTRING func_name_cstring() const override
  {
    static LEX_CSTRING name= {STRING_WITH_LEN("to_number") };
    return name;
  }
  Item *do_get_copy(THD *thd) const override { return nullptr; }


  bool fix_length_and_dec_double()
  {
    set_maybe_null();
    decimals= NOT_FIXED_DEC;
    max_length= float_length(decimals);
    return false;
  }

  // A helper abstract class, to define fix_length_and_dec().
  class Ha_double: public Item_handled_func::Handler_double
  {
  public:
    bool fix_length_and_dec(Item_handled_func *func) const override
    {
      DBUG_ASSERT(dynamic_cast<Item_func_to_number*>(func));
      Item_func_to_number *tfunc= static_cast<Item_func_to_number*>(func);
      return tfunc->fix_length_and_dec_double();
    }
  };


  /*
     Used in cases when arg_count==1:
       to_number('123')
  */
  double val_real_without_format()
  {
    DBUG_EXECUTE_IF("numconv_format", null_value= false; return 0;);
    StringBuffer<STRING_BUFFER_USUAL_SIZE> subject_buffer;
    String *subject;
    if ((null_value= !(subject= args[0]->val_str(&subject_buffer))))
      return 0;
    return double_from_string_with_check(subject);
  }

  class Ha_double_without_format: public Ha_double
  {
  public:
    double val_real(Item_handled_func *func) const override
    {
      DBUG_ASSERT(dynamic_cast<Item_func_to_number*>(func));
      Item_func_to_number *tfunc= static_cast<Item_func_to_number*>(func);
      return tfunc->val_real_without_format();
    }
    static const Ha_double_without_format s_singleton;
  };


  /*
    Used for the cases when the format consists only of
    integer digit with commas used as group separators.
  */
  double val_real_group_comma(const Format_parser::Format::Container & format)
  {
    DBUG_EXECUTE_IF("numconv_format", null_value= false; return 0;);
    StringBuffer<STRING_BUFFER_USUAL_SIZE> subject_buffer;
    String *sbj= args[0]->val_str(&subject_buffer);// The string to convert
    if ((null_value= !(sbj)))
      return 0;
    const Double_null nr= format.Integer::to_dbln_no_G(sbj->to_lex_cstring(),
                                                       sbj->charset());
    null_value= nr.is_null();
    return (double) nr.value();
  }

  class Ha_double_using_group_comma: public Ha_double
  {
  public:
    double val_real(Item_handled_func *func) const override
    {
      DBUG_ASSERT(dynamic_cast<Item_func_to_number*>(func));
      Item_func_to_number *tfunc= static_cast<Item_func_to_number*>(func);
      return tfunc->val_real_group_comma(tfunc->m_format);
    }
    static const Ha_double_using_group_comma s_singleton;
  };


  /*
    Format detected per row
  */
  double val_real_with_format_per_row()
  {
    auto const level= Sql_state_errno_level::WARN_LEVEL_WARN;
    StringBuffer<STRING_BUFFER_USUAL_SIZE> subject_buffer;
    String *sbj, *fmt;
    if ((null_value= !(sbj= args[0]->val_str(&subject_buffer))||
                     !(fmt= args[1]->val_str(&m_format_buffer))))
      return 0;
    // Parse the format and validate it
    m_parser= Format_parser(current_thd, func_name_cstring(),
                            args[1]->collation.collation,
                            fmt->to_lex_cstring());
    m_format= Format_parser::Goal(&m_parser);
    if ((null_value= m_format.check(m_parser, level)))
      return 0;
    const Handler *ha= func_handler_by_format(m_format, m_parser, level);
    return ha->val_real(this);
  }


  class Ha_double_with_format_per_row: public Ha_double
  {
  public:
    double val_real(Item_handled_func *func) const override
    {
      DBUG_ASSERT(dynamic_cast<Item_func_to_number*>(func));
      Item_func_to_number *tfunc= static_cast<Item_func_to_number*>(func);
      return tfunc->val_real_with_format_per_row();
    }
    static const Ha_double_with_format_per_row s_singleton;
  };


  const Item_handled_func::Handler *
  func_handler_by_format(const Format_parser::Goal & format,
                         const Format_parser & parser,
                         Sql_state_errno_level::enum_warning_level level)
                                                                    const
  {
    if (format.Format_TM::length())
      return &Ha_double_without_format::s_singleton;

    const Format_parser::feature_t format_features= format.features();
    Format_parser::feature_t fmt1= (Format_parser::feature_t)
                                   (Format_parser::F_INT_DIGIT |
                                    Format_parser::F_INT_GROUP_COMMA |
                                    Format_parser::F_INT_B |
                                    Format_parser::F_INT_DOLLAR |
                                    Format_parser::F_PREF_DOLLAR |
                                    Format_parser::F_PREF_B);
    if ((format_features & ~fmt1) == 0)
      return &Ha_double_using_group_comma::s_singleton;
    // TODO: more formats
    return &Ha_double_without_format::s_singleton;
  }

  bool fix_length_and_dec(THD *thd) override
  {
    if (arg_count == 1) // to_number('123')
    {
      set_func_handler(&Ha_double_without_format::s_singleton);
    }
    else if (args[1]->can_eval_in_optimize()) // to_number('123',const_expr)
    {
      /*
        If args[1] is a contant, then evaluate the format, parse and cache
        the parsed format, to avoid its evaluation and parsing per row.
      */
      if (set_func_handler_for_const_format(thd))
        return true;
    }
    else // The format is not constant
      set_func_handler(&Ha_double_with_format_per_row::s_singleton);
    return m_func_handler->fix_length_and_dec(this);
  }


  bool set_func_handler_for_const_format(THD *thd)
  {
    const auto level= Sql_state_errno_level::WARN_LEVEL_ERROR;
    // Evaluate the format and cache its value in m_format_buffer.
    String *fmt= args[1]->val_str(&m_format_buffer);
    if (!fmt || (fmt != &m_format_buffer && m_format_buffer.copy(*fmt)))
      return null_value= true;// SQL NULL or EOM
    // Parse the format and validate it
    m_parser= Format_parser(thd, func_name_cstring(),
                            args[1]->collation.collation,
                            fmt->to_lex_cstring());
    m_format= std::move(Format_parser::Goal(&m_parser));
    if ((null_value= m_format.check(m_parser, level)))
      return true;
    DBUG_EXECUTE_IF("numconv_format", (m_format.print_as_note()););
    // Determine the handler
    const Handler *ha= func_handler_by_format(m_format, m_parser, level);
    set_func_handler(ha);
    return false;
  }

};


const Item_func_to_number::Ha_double_without_format
  Item_func_to_number::Ha_double_without_format::s_singleton;

const Item_func_to_number::Ha_double_using_group_comma
  Item_func_to_number::Ha_double_using_group_comma::s_singleton;

const Item_func_to_number::Ha_double_with_format_per_row
  Item_func_to_number::Ha_double_with_format_per_row::s_singleton;


class Create_func_to_number : public Create_native_func
{
public:
  Item *create_native(THD *thd, const LEX_CSTRING *name,
                     List<Item> * args) override
  {
    if (unlikely(!args || args->elements < 1 || args->elements > 2))
    {
      my_error(ER_WRONG_PARAMCOUNT_TO_NATIVE_FCT, MYF(0), name->str);
      return NULL;
    }
    return new (thd->mem_root) Item_func_to_number(thd, *args);
  }

  static Create_func_to_number s_singleton;

protected:
  Create_func_to_number() = default;
  ~Create_func_to_number() override = default;
};

Create_func_to_number Create_func_to_number::s_singleton;
Create_func & create_func_to_number= Create_func_to_number::s_singleton;
