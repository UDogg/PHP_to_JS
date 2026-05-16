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
        //
        if(Schema::hasTable('users'))
        {
            Schema::table('users', function (Blueprint $table) {
                $table->enum('is_admin',['Y','N'])->default('N');
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasColumn('users', 'is_admin')) {
            Schema::table('users', function (Blueprint $table) {
                $table->dropColumn('is_admin');
            });
        }

    }
};
