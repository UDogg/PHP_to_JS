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
        if (!Schema::hasColumn('users', 'list_flag')) {
            Schema::table('users', function (Blueprint $table) {
                $table->string('list_flag',50)->nullable();
                      
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
       if (Schema::hasColumn('users', 'list_flag')) {
            Schema::table('users', function (Blueprint $table) {
                $table->dropColumn('list_flag');
            });
        }
    }
};
