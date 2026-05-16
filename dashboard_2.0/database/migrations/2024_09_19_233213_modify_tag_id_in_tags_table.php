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

            Schema::table('tag_names', function (Blueprint $table) {
                $table->unsignedBigInteger('tag_id')->change();
            });

    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {

            Schema::table('tag_names', function (Blueprint $table) {
                $table->bigInteger('tag_id')->change();
            });

    }
};
