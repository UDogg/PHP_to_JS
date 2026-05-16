<?php
use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('data_export_log', function (Blueprint $table) {
            if (!Schema::hasColumn('data_export_log', 'user_id')) {
                $table->integer('user_id');
            }

            if (!Schema::hasColumn('data_export_log', 'uid')) {
                $table->string('uid');
                $table->index('uid');
            }

            if (!Schema::hasColumn('data_export_log', 'request')) {
                $table->text('request');
            }

            if (!Schema::hasColumn('data_export_log', 'file_expiry')) {
                $table->dateTime('file_expiry');
            }

            if (Schema::hasColumn('data_export_log', 'file_deleted')) {
                $table->integer('file_deleted')->nullable()->change();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('data_export_log', function (Blueprint $table) {
            if (Schema::hasColumn('data_export_log', 'user_id')) {
                $table->dropColumn('user_id');
            }
              if (Schema::hasColumn('data_export_log', 'userid')) {
                $table->dropColumn('userid');
            }

            if (Schema::hasColumn('data_export_log', 'uid')) {
                $table->dropColumn('uid');
            }

            if (Schema::hasColumn('data_export_log', 'request')) {
                $table->dropColumn('request');
            }

            if (Schema::hasColumn('data_export_log', 'file_expiry')) {
                $table->dropColumn('file_expiry');
            }

            if (Schema::hasColumn('data_export_log', 'file_deleted')) {
                $table->integer('file_deleted')->nullable(false)->change();
            }
        });
    }
};
