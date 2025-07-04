/* Copyright (C) 2015-2025 Codership Oy <info@codership.com>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */


#ifndef WSREP_SCHEMA_H
#define WSREP_SCHEMA_H

/* wsrep-lib */
#include "wsrep_types.h"

#include "mysqld.h"
#include "wsrep_mysqld.h"
/*
  Forward decls
*/
class THD;
class Relay_log_info;
struct TABLE;
struct TABLE_LIST;
struct st_mysql_lex_string;
typedef struct st_mysql_lex_string LEX_STRING;
class Gtid_log_event;

/** Name of the table in `wsrep_schema_str` used for storing streaming
replication data. In an InnoDB full format, e.g. "database/tablename". */
extern const char* wsrep_sr_table_name_full;

class Wsrep_schema
{
 public:

  Wsrep_schema();
  ~Wsrep_schema();

  /*
    Initialize wsrep schema. Storage engines must be running before
    calling this function.
  */
  int init();

  /*
    Store wsrep view info into wsrep schema.
  */
  int store_view(THD*, const Wsrep_view& view);

  /*
    Restore view info from stable storage.
  */
  Wsrep_view restore_view(THD* thd, const Wsrep_id& own_id) const;

  /**
    Append transaction fragment to fragment storage.
    Transaction must have been started for THD before this call.
    In order to make changes durable, transaction must be committed
    separately after this call.

    @param thd THD object
    @param server_id Wsrep server identifier
    @param transaction_id Transaction identifier
    @param flags Flags for the fragment
    @param data Fragment data buffer

    @return Zero in case of success, non-zero on failure.
  */
  int append_fragment(THD* thd,
                      const wsrep::id& server_id,
                      wsrep::transaction_id transaction_id,
                      wsrep::seqno seqno,
                      int flags,
                      const wsrep::const_buffer& data);
  /**
     Update existing fragment meta data. The fragment must have been
     inserted before using append_fragment().

     @param thd THD object
     @param ws_meta Wsrep meta data

     @return Zero in case of success, non-zero on failure.
   */
  int update_fragment_meta(THD* thd,
                           const wsrep::ws_meta& ws_meta);

  /**
     Remove fragments from storage. This method must be called
     inside active transaction. Fragment removal will be committed
     once the transaction commits.

     @param thd Pointer to THD object
     @param server_id Identifier of the running server
     @param transaction_id Identifier of the current transaction
     @param fragments Vector of fragment seqnos to be removed
  */
  int remove_fragments(THD*                             thd,
                       const wsrep::id&                 server_id,
                       wsrep::transaction_id            transaction_id,
                       const std::vector<wsrep::seqno>& fragments);

  /**
     Replay a transaction from stored fragments. The caller must have
     started a transaction for a thd.

     @param thd Pointer to THD object
     @param ws_meta Write set meta data for commit fragment.
     @param fragments Vector of fragments to be replayed

     @return Zero on success, non-zero on failure.
  */
  int replay_transaction(THD* thd,
                         Relay_log_info* rli,
                         const wsrep::ws_meta& ws_meta,
                         const std::vector<wsrep::seqno>& fragments);

  /**
     Recover streaming transactions from SR table.
     This method should be called after storage engines are initialized.
     It will scan SR table and replay found streaming transactions.

     @param orig_thd The THD object of the calling thread.

     @return Zero on success, non-zero on failure.
  */
  int recover_sr_transactions(THD* orig_thd);

  /**
     Store GTID-event to mysql.gtid_slave_pos table.

     @param thd  The THD object of the calling thread.
     @param gtid GTID event from binlog.

     @return Zero on success, non-zero on failure.
  */
  int store_gtid_event(THD* thd, const Gtid_log_event *gtid);

  /**
     Delete all rows on bootstrap from `wsrep_allowlist` variable
  */
  void clear_allowlist();

  /**
     Store allowlist ip on bootstrap from `wsrep_allowlist` variable
  */
  void store_allowlist(std::vector<std::string>& ip_allowlist);

  /**
     Scan white list table against accepted connection. Allow if ip
     is found in table or if table is empty.

     @param key   Which allowlist column to compare
     @param value Value to be checked against allowlist
     
     @return True if found or empty table, false on not found 
  */
  bool allowlist_check(Wsrep_allowlist_key key, const std::string& val);

 private:
  /* Non-copyable */
  Wsrep_schema(const Wsrep_schema&);
  Wsrep_schema& operator=(const Wsrep_schema&);
};

extern Wsrep_schema* wsrep_schema;

extern LEX_CSTRING WSREP_LEX_STREAMING;
extern LEX_CSTRING WSREP_LEX_CLUSTER;
extern LEX_CSTRING WSREP_LEX_MEMBERS;
extern LEX_CSTRING WSREP_LEX_ALLOWLIST;

#endif /* !WSREP_SCHEMA_H */
