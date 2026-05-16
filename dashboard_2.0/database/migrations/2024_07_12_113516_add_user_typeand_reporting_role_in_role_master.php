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
        Schema::table('roles', function (Blueprint $table) {
            if(!Schema::hasColumn('roles', 'user_type')){
                $table->integer('user_type')->nullable();
            }
            if(!Schema::hasColumn('roles', 'reporting_role')){
                $table->integer('reporting_role')->nullable()->comment("Reporting Role current table id ");
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('roles', function (Blueprint $table) {
            //
        });
    }
};
