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
        Schema::table('users', function (Blueprint $table) {
            $table->string('dob')->nullable()->after('last_name');
            $table->string('license_start_date')->nullable()->after('dob');
            $table->string('license_end_date')->nullable()->after('license_start_date');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::table('users', function (Blueprint $table) {
            $table->dropColumn('dob');
        });
    }
};
