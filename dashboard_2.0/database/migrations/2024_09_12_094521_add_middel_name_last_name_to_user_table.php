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
        if (Schema::hasTable('users')) {
            Schema::table('users', function (Blueprint $table) {
                if (!Schema::hasColumn('users', 'middle_name') && !Schema::hasColumn('users', 'last_name')) {
                    $table->string('middle_name')->after('name')->nullable();
                    $table->string('last_name')->after('middle_name')->nullable();
                }
            });
        }
    }

    public function down(): void
    {
        if (Schema::hasTable('users')) {
            Schema::table('users', function (Blueprint $table) {
                if (Schema::hasColumn('users', 'middle_name')) {
                    $table->dropColumn('middle_name');
                }
                if (Schema::hasColumn('users', 'last_name')) {
                    $table->dropColumn('last_name');
                }
            });
        }
    }
};
