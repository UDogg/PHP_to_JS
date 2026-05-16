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
        if (Schema::hasTable('master_companies')) {
            Schema::table('master_companies', function (Blueprint $table) {
                if (!Schema::hasColumn('master_companies', 'lobname')) {
                    $table->enum('lobname', ['HEALTH', 'MOTOR'])->nullable()->after('company_id');
                }
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasTable('master_companies')) {
            Schema::table('master_companies', function (Blueprint $table) {
                if (Schema::hasColumn('master_companies', 'lobname')) {
                    $table->dropColumn('lobname');
                }
            });
        }
    }
};
